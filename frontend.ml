open Ll
open Ctxt
open Ast

(* Overview ----------------------------------------------------------------- *)

(* The job of the frontend is to translate the abstract syntax into
   the LLVM IR, implementing the source language semantics in terms of
   the target language constructs.

   Because the LLVM IR is typed, the frontend must also propagate
   enough type information so that we can generate appropriate type
   annotations at the LLVM level.  For Oat v.1, the type system is
   simple enough that the frontend can typecheck the abstract syntax
   during the compilation process.  The structure of the compiler
   therefore mirrors the form of the Oat source language typechecking
   rules, which are available from the project web pages.                     *)


(* Instruction Streams ------------------------------------------------------ *)

(* The compiler emits code by generating a stream of instructions interleaved
   with labels and values (like string constants) that should be hoisted to
   the global scope.  

   The result of each translation function (typically) includes a stream.     *)
type elt = 
  | L of lbl                (* Block labels *)
  | I of uid * insn         (* LL IR instruction *)
  | T of terminator         (* Block terminators *)
  | G of gid * Ll.gdecl     (* Hoisted Globals (usually strings) *)

type stream = elt list

(* This is occassionally useful for debugging.                                *)
let string_of_elt = function
  | L lbl         -> Printf.sprintf "L: %s" lbl
  | I (uid, insn) -> Printf.sprintf "I: %s = %s" uid (Ll.string_of_insn insn)
  | T t           -> Printf.sprintf "T: %s" (Ll.string_of_terminator t)
  | G (gid, g)    -> Printf.sprintf "G: %s = %s" gid (Ll.string_of_gdecl g)


(* During generation, we typically emit code so that it is in
   _reverse_ order when the stream is viewed as a list.  That is,
   instructions closer to the head of the list are to be executed
   later in the program.  That is because cons is more efficient than
   append.

   To help make code generation easier, we define snoc (reverse cons)
   and reverse append, which let us write code sequences in their
   natural order.                                                             *)
let ( >@ ) x y = y @ x
let ( >:: ) x y = y :: x


(* Convert an instruction stream into a control flow graph and a list
   of globals.

   - assumes that the instructions are in 'reverse' order of execution.

   - the returned global declarations are the "hoisted" string
     constants that appear in the function body

     For example, the source oat program:

     string f() { return "a fresh string"; }

     would translate to LL code that introduces a new global string
     constant (gid, (str_arr_typ, GString "a fresh string")).
     The string constant is introduced by the cmp_const function.             *)
let build_cfg (code:stream) : Ll.cfg * (Ll.gid * Ll.gdecl) list  =
  let blocks_of_stream (code:stream) =
    let (gs, insns, term_opt, blks) =  List.fold_left
	(fun ((gs:(Ll.gid * Ll.gdecl) list), insns, term_opt, blks) e ->
           begin match e with
             | L l ->
               begin match term_opt with
                 | None ->
                   if (List.length insns) = 0 then  (gs, [], None, blks)
                   else failwith @@
                     Printf.sprintf "build_cfg: block labeled %s has\
                                     no terminator" l
                     
                 | Some terminator ->
                   (gs, [], None, (l, {insns; terminator})::blks)
               end
             | T t  -> (gs, [], Some t, blks)
             | I (uid,insn)  -> (gs, (uid,insn)::insns, term_opt, blks)
             | G (gid,gdecl) ->  ((gid,gdecl)::gs, insns, term_opt, blks)
           end)
        ([], [], None, []) code
    in
    begin match term_opt with
      | None -> failwith "build_cfg: entry block has no terminator" 
      | Some terminator ->
        ({insns; terminator}, blks), gs
    end
  in
    blocks_of_stream code 

type t = Ast.typ



(* array helpers *)
let str_arr_typ s = Array(1 + String.length s, I8)
let elt_typ_of_arr t : typ =
  match t with 
  | {elt=TRef({elt=RArray(t)})} -> t
  | _ -> failwith "compiler error: elt_typ_of_arr"

let prefix_of l =
  begin match List.rev l with
    | x::rest -> (List.rev rest), x
    | _ -> failwith @@ Printf.sprintf "compiler error: illegal path index"
  end

(* Compiling Types ---------------------------------------------------------- *)
(* Compile Oat types to LLVM types.  Arrays are represented as a
   pointer to a structure of the form {i64, [0 x t]}.  The first i64
   stores the size of the array.  A C-style string is stored as a
   pointer to an array of chars, with no length information, since Oat
   strings are immutable.

   NOTE: cmp_typ is the translation of the *expression* types of the
   language.  Thus a source expression of type t will have LL type
   (cmpt_typ t) while a source path of type t will have LL type
   Ptr(cmp_ty t) when used on the left-hand side of an assignment.            *)

let t_int  : Ll.ty = I64
let t_bool : Ll.ty = I1
let t_str  : Ll.ty = Ptr I8


(* named types -------------------------------------------------------------- *)
let class_struct_name cid = (Printf.sprintf "_class_%s" cid)
let class_named_ty cid =
  Ll.Namedt (class_struct_name cid)
let object_named_ty (cid:string) =
  Ll.Namedt (Printf.sprintf "%s" cid)


(* translate OAT types to LLVM types ---------------------------------------- *)
let rec cmp_typ (t:Ast.typ) =
  match t.elt with
  | Ast.TBool   -> t_bool
  | Ast.TInt    -> t_int
  | Ast.TNull   -> Ptr t_int
  | Ast.TRef r  -> Ptr (cmp_ref r)  (* not null *)
  | Ast.TNRef r -> Ptr (cmp_ref r)  (* possibly null *)

and cmp_ref (r:Ast.ref) =
  match r.elt with
  | Ast.RString  -> I8
  | Ast.RArray u -> Struct [I64; Array(0, cmp_typ u)]
  | Ast.RClass c -> object_named_ty c.elt

(* return types *)
let cmp_rtyp r =
  match r with
  | None -> Void
  | Some t -> cmp_typ t

(* function / method types *)
let cmp_ftyp ((args,ret):Ast.ftyp) : Ll.fty = 
  (List.map cmp_typ args, cmp_rtyp ret)

(* names for global values associated with classes -------------------------- *)
let vtbl_name cid = Printf.sprintf "_vtbl_%s" cid
let ctr_name cid  = Printf.sprintf "_new_%s" cid
let method_name cid mth = Printf.sprintf "_%s_%s" mth cid


(* compile a method signature ----------------------------------------------- *)

(* Produces the function pointer and global value for a given method 
   as seen from class 'cid'.

    - the 'this' parameter type of the method depends on the class 
      that implements the method (which, if is inherited, may not be cid)

    - the global name likewise depends on the implementing class              *)
let cmp_method_sig (cid:string) (mth:string)
    ((stat, (ts, r)) :Tctxt.status * Ast.ftyp)
  : Ll.ty * Ll.ginit
  
  =
  let cls =
    match stat with
      | Tctxt.Extended | Tctxt.Overridden -> cid
      | Tctxt.Inherited s -> s
  in    
  let this_arg = ast_class_typ @@ no_loc cls in
  (Ptr (Fun (cmp_ftyp (this_arg::ts, r)))), (GGid (method_name cls mth))


(* vtables ------------------------------------------------------------------ *)
(* Computes
     - an LLVM struct type describing the structure of a class' vtable
     - a global value that is the vtable 

   The vtable for a class C that has methods m1 .. mN is a structure in
   memory laid out as:
        ptr to super;     // pointer to the parent's vtable
        ptr to m1;        // function pointer to code for m1
        ...
        ptr to mN;        // function pointer to code for mN                  *)
let class_to_vtbl cid (i:Tctxt.interface) : (Ll.tid * Ll.ty) * (Ll.ginit) =
  let tid = class_struct_name cid in 
  let super_ptr_ty = Ptr  (class_named_ty i.Tctxt.sup.elt) in
  let super_ptr    = GGid (vtbl_name i.Tctxt.sup.elt) in
  let method_typs_gids =
    List.map (fun (f, sftyp) -> cmp_method_sig cid f sftyp) i.Tctxt.mths
      
  in
  let gs = (super_ptr_ty, super_ptr)::method_typs_gids in
  let tys = List.map fst gs in
  (tid, Struct tys), (GStruct gs) 

(* object structure --------------------------------------------------------- *)
(* Computes an LLVM struct type describing the structure of an object.
    
   The object for a class C that has fields f1 .. fN is a structre in 
   memory laid out as:
        ptr to _vtbl_C     // pointer to C's vtable a.k.a the 'dynamic class'
        slot for f1        // value of the field f1
        ...
        slot for nN        // vale of the field fN                            *)
let object_ty name (i:Tctxt.interface) : (Ll.tid * Ll.ty) =
  let vtbl_ptr = Ptr (class_named_ty name) in
  let fields = List.map (fun (_, t) -> cmp_typ t) i.Tctxt.flds in
  name, Struct (vtbl_ptr :: fields)


    
(* LL IR helper functions --------------------------------------------------- *)

(* Generate a fresh identifier based on a given string.  Because Oat 
   identifiers cannot begin with _ the resulting string is guaranteed
   not to clash with another source language construct.                       *)
let gensym : string -> string =
  let c = ref 0 in
  fun (s:string) -> incr c; Printf.sprintf "_%s__%d" s (!c)

(* Compile Ocaml constants to LL IR constant operands of the right type.      *)
let i1_op_of_bool b   = Ll.Const (if b then 1L else 0L)
let i64_op_of_int i   = Ll.Const (Int64.of_int i)
let i64_op_of_int64 i = Ll.Const i

(* Compute a gep path to index into an Oat array represented as LL type:
    {i64, [ 0 x u] }*                                                         *)
let gep_array_index (i:operand) = [
  i64_op_of_int 0;   (* dereference the pointer *)
  i64_op_of_int 1;   (* focus on the array component of the struct *)
  i;                 (* index into the array *)
]

(* Compute a gep path to the length field of an Oat array.                    *)
let gep_array_len = [
  i64_op_of_int 0;  (* dereference the pointer *)
  i64_op_of_int 0;  (* focus on the length component of the struct *)
]

(* The same gep paths work for other datastructures too *)
let gep_vtbl_ptr = gep_array_len
let gep_super_ptr = gep_array_len

let index_of x l =
  let rec loop l i =
    match l with
    | [] -> failwith "compiler error: index_of not found"
    | y::rest -> if x = y then i else loop rest (i+1)
  in
  loop l 0

(* Gep path for field access in class cid ----------------------------------- *)
let gep_for_field h cid fid =
  let iface = Tctxt.lookup_interface cid.elt h in
  let ind = index_of fid.elt (List.map fst iface.Tctxt.flds) in
  [ i64_op_of_int 0  (* dereference the pointer *)
  ; i64_op_of_int (ind + 1)  (* skip the vtable ptr to find the field *)
  ]

(* Gep path for method access in vtable for class cid ----------------------- *)
let gep_for_method h cid mid =
  let iface = Tctxt.lookup_interface cid.elt h in
  let ind = index_of mid.elt (List.map fst iface.Tctxt.mths) in
  [ i64_op_of_int 0  (* dereference the pointer *)
  ; i64_op_of_int (ind + 1)  (* skip the super class ptr to find the method *)
  ]
  

(* Generate a call to the runtime.c function oat_alloc_array.  t is
   the src type size is an i64 operand, the number of elements in the
   array returns: an operand of type (cmp_ty (Ast.TArray t)) and the
   code for allocating the array.  Note that because oat_alloc_array is
   polymorphic (its proper return type is generic in the element type),
   we have to use the Bitcast operation to let LL IR know what type the
   array should have.                                                         *)

let oat_alloc_array_dynamic (t:Ast.typ) (size:operand) : operand * stream =
  let ans_id = gensym "arr_" in
  let ans_ty = cmp_typ @@ ast_array_typ t in
  let arr_id = gensym "rarr" in
  let arr_ty = cmp_typ @@ ast_array_typ ast_int in
  (Id ans_id,
   [ I (arr_id, Call(arr_ty, Gid "oat_alloc_array", [(I64, size)])) ] >::
   I (ans_id, Bitcast(arr_ty, Id arr_id, ans_ty))) 

let oat_alloc_array_static (t:Ast.typ) (n:int) : operand * stream=
  oat_alloc_array_dynamic t (Ll.Const(Int64.of_int n))

(* Generate code to write eop to the array index i of array array_op.
   Note that array_op has LL type cmp_ty (TArray t) = Ptr ((Struct
   [I64; Array(0, cmp_ty u)]) So generate a getelementptr instruction
   to index into the array.  *)
let cmp_array_update_static (ll_arr_ty:Ll.ty) (ll_elt_ty:Ll.ty) (i:int)
    (array_op:operand) (eop:operand) : stream =
  let ind = gensym "ind_" in
  [ I (ind, Gep(ll_arr_ty, array_op, gep_array_index @@ i64_op_of_int i)) ] >::
  (I ("",  Store(ll_elt_ty, eop, Id ind)))


(* Compile a source binop  -------------------------------------------------- *)
let cmp_binop t (b : Ast.binop) : Ll.operand -> Ll.operand -> Ll.insn  =
  let ib b op1 op2 = (Ll.Binop (b, t, op1, op2)) in
  let ic c op1 op2 = (Ll.Icmp (c, t, op1, op2)) in
  match b with
  | Ast.Add  -> ib Ll.Add
  | Ast.Mul  -> ib Ll.Mul
  | Ast.Sub  -> ib Ll.Sub
  | Ast.And  -> ib Ll.And
  | Ast.IAnd -> ib Ll.And 
  | Ast.IOr  -> ib Ll.Or
  | Ast.Or   -> ib Ll.Or
  | Ast.Shl  -> ib Ll.Shl
  | Ast.Shr  -> ib Ll.Lshr
  | Ast.Sar  -> ib Ll.Ashr

  | Ast.Eq   -> ic Ll.Eq
  | Ast.Neq  -> ic Ll.Ne
  | Ast.Lt   -> ic Ll.Slt
  | Ast.Lte  -> ic Ll.Sle
  | Ast.Gt   -> ic Ll.Sgt
  | Ast.Gte  -> ic Ll.Sge


(* compiling subtyping checks ----------------------------------------------- *)
(* Each use of assert_subtype, which checks that an expression of type
   t is a subype of u, is a possible place where the LLVM IR type for
   the expression 'e' and its use by the 'consumer of e' might not
   match.

   Therefore, at the LLVM level, we need to introduce type casts that
   explicitly describe the change of type from t to u.  This is always
   safe because if t <: u according to the type system, then
   (cmp_typ t) can be bitcast to (cmp_typ u) in the LLVM without 
   introducting errors.

    - assumes that src_ty is the type associated with operand op
    - introduces a bitcast instruction if needed to convert
      from src_ty to dst_ty                                                   *)
let bitcast_if_needed (src_ty:Ll.ty) (dst_ty:Ll.ty) (op:operand)
    : operand * stream  =
  if src_ty = dst_ty then op, [] else
    let ans = gensym "cast" in
    (Id ans), [I(ans, Bitcast(src_ty, op, dst_ty))]

let ty (t:t) (x:'a) : ('a, t) loc = {elt=x; ext=t; loc=Range.norange}


 
(* Compile a constant ------------------------------------------------------- *)

(* Invariant: cn is a source constant that should be checked to have
   type source type t.  The result is the compiled type, an operand of
   that type and a stream that correctly initializes the operand. 

   Unlike global constants (handled by the cmp_init function), constant 
   arrays that appear in function bodies need to allocate fresh storage.
   Otherwise, two calls to the function f below would return the _same_
   reference, when each call should create a fresh copy of the array.

    int[] f() {
      return {1;2;3}
    }

   For CArr, the compiler emits code that allocates a fresh array 
   and then initializes it with the constant values.                          *)
let rec cmp_const (cn:t Ast.const) : Ll.ty * Ll.operand * stream =
  match cn.elt with
  | Ast.CNull    -> (Ptr I8, Null, [])
  | Ast.CBool(b) -> (t_bool, i1_op_of_bool b, [])
  | Ast.CInt(i)  -> (t_int, i64_op_of_int64 i ,[])
  | Ast.CStr(s)  ->
    let gid = gensym "sarr" in
    let str_arr_typ = str_arr_typ s in
    let uid = gensym "str_" in
    (t_str, Id uid,
     [G (gid, (str_arr_typ, GString s));
      I (uid, (Gep(Ptr(str_arr_typ), Gid gid, [Const 0L; Const 0L;])))
     ])

  | Ast.CArr(cs) ->
    let n = List.length cs in
    let u = elt_typ_of_arr cn.ext in
    let dst_elt_ty = cmp_typ u in
    let _, elts, elt_code =
      List.fold_left (fun (i, elts, s) elt ->
          let src_elt_ty, elt_op, elt_code = cmp_const elt in
          let elt_op, cast_code =
            bitcast_if_needed src_elt_ty dst_elt_ty elt_op
          in
          (i+1,
           (i, elt_op)::elts,
           elt_code >@ cast_code >@ s
          ))
        (0, [], []) cs
    in
    let arr, alloc_code = oat_alloc_array_static u n in
    let ll_arr_ty = Struct [I64; Array(0, dst_elt_ty)] in
    let store_code = List.map
        (fun (i,elt_op) ->
           cmp_array_update_static ll_arr_ty dst_elt_ty i arr elt_op)
        elts |> List.flatten
    in
    (ll_arr_ty, arr, alloc_code >@ elt_code >@ store_code)


(* compile and identifier --------------------------------------------------- *)
(* The typechecker ensures that fields are qualified with 'this',
   so the frontend can assume that identifiers are either local 
   or global variables.                                                       *)    
let cmp_id (c:ctxt) (t:typ) (x:id) : Ll.operand * stream =
  try
    let (id,_) = lookup_local x.elt c in
    Id(id), []
  with
    Not_found -> try
      let id, _, ll_ty = lookup_global x.elt c in
      let src_ty = Ptr ll_ty in
      let dst_ty = Ptr (cmp_typ t) in
      let op, bitcast_code = bitcast_if_needed src_ty dst_ty (Gid id) in
      op, bitcast_code

    with Not_found ->
      failwith @@
      Printf.sprintf "compiler error: cmp_id dentifier %s at %s not found"
        x.elt (Range.string_of_range x.loc)



(* Compile an expression ---------------------------------------------------- *)

(* Invariant: assumes that exp has source type  exp.elt, and returns the 
   corresponding LL type, an operand of that type, and a stream of
   instructions that computes the value of the operand.

   - the output LL ty will always be (cmp_typ exp.elt)

   NOTE: for HW 5 you need only complete the NewObj case                      *)
let rec cmp_exp h (c:ctxt) (exp:t exp) : (Ll.ty * Ll.operand * stream) =
  match exp.elt with
  | Ast.Const cn -> cmp_const cn

  (* Polymorphic handling of == *)
  | Ast.Bop (Eq|Neq as bop, e1, e2) ->
    let (t1, op1, code1) = cmp_exp h c e1 in
    let (t2, op2, code2) = cmp_exp h c e2 in
    let (dst_ty, op1, bitcast_code1, op2, bitcast_code2) =
      if t1 = t2 then (t1, op1, [], op2, [])
      else
        let dst_ty = Ptr I8 in
        let op1, bitcast_code1 = bitcast_if_needed t1 dst_ty op1 in
        let op2, bitcast_code2 = bitcast_if_needed t2 dst_ty op2 in
        (dst_ty, op1, bitcast_code1, op2, bitcast_code2)
    in
    let ans_id = gensym "bop_" in 
    (cmp_typ exp.ext,
     (Id ans_id), code1 >@ bitcast_code1 >@ code2 >@ bitcast_code2 >:: I (ans_id, cmp_binop dst_ty bop op1 op2))
    
  | Ast.Bop (bop, e1, e2) ->
    let (t, op1, code1) = cmp_exp h c e1 in
    let (_, op2, code2) = cmp_exp h c e2 in
    let ans_id = gensym "bop_" in 
    (cmp_typ exp.ext,
     (Id ans_id), code1 >@ code2 >:: I (ans_id, cmp_binop t bop op1 op2))
    
  | Ast.Uop (uop, e) ->
    let (_, op, code) = cmp_exp h c e in
    let ans_id = gensym "unop" in
    (cmp_typ exp.ext,
     (Id ans_id),
     code >::
     I (ans_id,
        begin match uop with
	  | Ast.Neg    -> Binop (Sub, I64, i64_op_of_int 0, op)
          | Ast.Lognot -> Icmp  (Eq, I64, op, i1_op_of_bool false)
          | Ast.Bitnot -> Binop (Xor, I64, op, i64_op_of_int (-1))
        end))

  | Ast.Path p -> 
    let t, op, code = cmp_path_exp h c p in
    (cmp_typ t), op, code

  | Ast.NewArr(elem_ty,e1,id,e2) ->
    let ast_int_exp i : t exp = ty ast_int @@ Const(ty ast_int @@ CInt(Int64.of_int i)) in
    let _, size, code_e1 = cmp_exp h c e1 in
    let array_ty = ast_array_typ elem_ty in
    let array_op, alloc_code = oat_alloc_array_dynamic elem_ty size in

    let id_path : t path = [((ty ast_int @@ Field(id)) : t accessor)] in
    let id_ast  : t exp  = ty ast_int @@ (Path id_path) in
    
      (* Set up the context to add the fresh loop variables *)
    let bound_id = gensym "bnd_" in
    let bound_ty = I64 in
    let bound_ast : t exp = ty ast_int @@ Path [ty ast_int @@ Field(no_loc bound_id)] in
    
    let c = add_local c (no_loc bound_id) (bound_id, ast_int) in

    let ptr_id = gensym "ptr_" in
    let ptr_ty = cmp_typ array_ty in
    let ptr_path : t path = [ty array_ty @@ Field(no_loc ptr_id); ty ast_int @@ Index(id_ast)] in
    let c = add_local c (no_loc ptr_id) (ptr_id, array_ty) in

    let _, loop_code = cmp_stmt h c None @@  
       ( ty ast_null (For([ty ast_null {ty=ast_int; id; init=ast_int_exp 0}],
                 Some (ty ast_bool @@ Bop(Lt, id_ast, bound_ast)),
                 Some (ty ast_null @@ Assn(id_path,
                                      ty ast_int @@ (Bop(Add, id_ast, ast_int_exp 1)))),
                 [ty ast_null @@ Assn(ptr_path, e2)])) : t stmt)  
    in
    (cmp_typ array_ty,
     array_op,
     code_e1 >@
     alloc_code >@
     [I (bound_id, Alloca(bound_ty))] >@
     [I ("", Store (I64, size, Id bound_id))] >@
     [I (ptr_id, Alloca(ptr_ty))] >@
     [I ("", Store (ptr_ty, array_op, Id ptr_id))] >@
     loop_code)


  (* NewObj ----------------------------------------------------------------- *)
  (* - generate a call to 'oat_malloc' of the appropriate size for the newly
       created object
     - compile the arguments to the constructor and call the constructor
     - bitcast the object pointer to the appropriate object type              *)
  | Ast.NewObj(cid, es) ->
    let args_l, args_s = List.fold_left
      (fun (l,s) x ->
        let llty, llop, stream = cmp_exp h c x in
        ([(llty,llop)] >@ l, s >@ stream)
      ) 
      ([], [])
      es in
    let newobj_id = gensym "newobj" in
    let ret_id = gensym "newobjret" in
    let class_ty = cmp_typ (ast_class_typ cid) in
    (* TODO: calculate the size *)
    let obj_size = Ll.Const 1337L in
    let ctr_id = ctr_name cid.elt in
    let string_ty = cmp_typ ast_str in
    let args_l = (string_ty, Id newobj_id)::args_l in
    let stream =
      args_s >@
      [I (newobj_id, Call(string_ty, Gid "oat_malloc", [I64, obj_size]))] >@
      [I ("", Call(Void, Gid ctr_id, args_l))] >@
      [I (ret_id, Bitcast(string_ty, Id newobj_id, class_ty))] in
    (class_ty, Id ret_id, stream)


(* length of array ---------------------------------------------------------- *)
(* This is a polymorphic global function, so we need to special case its
   compilation.                                                               *)
and cmp_length_of_array h c es : operand * stream =
  begin match es with
    | [e] ->
      let ll_ty, arr_op, arr_code = cmp_exp h c e in
      let aptr = gensym "aptr" in
      let rslt = gensym "rslt" in
      Id rslt,
      arr_code >::
      I (aptr, Gep(ll_ty, arr_op, gep_array_len)) >::
      I (rslt, Load(Ptr I64, Id aptr))

    | _ -> failwith "compiler error: length_of_array got illegal args"
  end


(* Compile a path as a left-hand-side --------------------------------------- *)

(* Assumes that p is a valid path for assignment, meaning that it is either:
    -  just an identifier (a.k.a. a local or global variable) 
    -  or, a non-empty prefix path of array type followed by a field
       or array index

    Example valid paths:
      Oat:         Ast path:
    x              [Field("x")]
    x[3].f         [Field("x"); Index(Const(3L)); Field("f")]
    x[3].m(3)[4]   [Field("x"); Index(Const(3L)); 
                    Call("m", [Const(3)]); Index(Const(4))]
    f(17)[3]       [Call("f", [Const(17)]); Index(Const(3))]
    this.x         [Field("this"); Field("x")]

   Invariant: the result of compiling a path as a lhs is the *source* type t
   of the path expression, an operand of type Ptr(cmp_typ t), and a stream
   that computes an address for the path  into the returned operand.         *)
and cmp_path_lhs h (c:ctxt) (p:t path) : Ast.typ * Ll.operand * stream =
  let prefix, acc = prefix_of p in
  begin match acc.elt with
    | Field(x) when prefix = [] ->
      (* must be a local or global variable *)
      let op, code = cmp_id c acc.ext x in 
      acc.ext, op, code

    | Field(x) ->
      (* definitely a field *)
      let t, path_op, path_code = cmp_path_exp h c prefix in
      begin match t.elt with
      | TRef({elt=RClass(cid)}) ->
        let ptr_id = gensym "fldp" in
        let gep_path = gep_for_field h cid x in
        acc.ext, (Id ptr_id),
        path_code >@
        [I(ptr_id, Gep(Ptr(object_named_ty cid.elt), path_op, gep_path))]
        
      | _ -> failwith "compiler error: field projection from non-class type"
      end

    | Index(ind) ->
      let t, path_op, path_code = cmp_path_exp h c prefix in
      let u = elt_typ_of_arr t in
      let _, ind_op, ind_code = cmp_exp h c ind in
      let ptr_id = gensym "indp" in
      let arr_ty = cmp_typ t in
      u, (Id ptr_id),
      path_code >@ ind_code >@
      [I(ptr_id, Gep(arr_ty, path_op, gep_array_index ind_op))]
      
    | _ -> failwith "compiler error: illegal left-hand side"
  end

(* compile the arguments to a function call --------------------------------- *)
(* puts in the appropriate bitcasts to handle subtyping                       *)
and cmp_args (h:Tctxt.hierarchy) (c:ctxt) (es:(t exp) list) (ts:(typ list)) :
  (Ll.ty * Ll.operand) list * stream=
  Printf.printf "%d %d\n" (List.length es) (List.length ts);
  let (args, args_code) = List.fold_left2
      (fun (args,code) e t ->
         let (arg_t, arg_op, arg_code) = cmp_exp h c e in
         let dst_ty = cmp_typ t in
         let op, bitcast_code = bitcast_if_needed arg_t dst_ty arg_op in
         ((dst_ty, op)::args,
          code @ (arg_code >@ bitcast_code))) ([],[]) es ts in
  let args  = List.rev args in
  args, args_code 

(* call a function / method ------------------------------------------------- *)
(*  - f is the LLVM  name of the function or method (i.e. it has already
      been appropriately name mangled                                         *)
and cmp_invocation (h:Tctxt.hierarchy) (c:ctxt)
    (f:operand) (es:(t exp) list) ((ts, rt):ftyp)
  : Ast.rtyp * Ll.operand * stream =

  let res_id = gensym "rslt" in
  let args, args_code = cmp_args h c es (ts:typ list) in
  rt,
  (Id res_id), 
  args_code >@
  [I(res_id, Call(cmp_rtyp rt, f, args))] 

(* compile a call ----------------------------------------------------------- *)
and cmp_call h c prefix acc : Ast.rtyp * Ll.operand * stream =

  (* produce a piece of abstract syntax for "this" at a given type *)
  let ast_this_var t =  ty t (Path([ty t @@ Field this_id])) in

  begin match acc.elt with
    | Call(f,es) ->
      begin match prefix with
        | [] ->
          (* Must be a global function - 'this' was put in by typechecker *)
          if f.elt = "length_of_array" then
            let op, code = cmp_length_of_array h c es in
            Some ast_int, op, code
          else
            let (_,ftyp) = lookup_function f.elt c in
            cmp_invocation h c (Gid f.elt) es ftyp


        (* super method invocation ------------------------------------------ *)
        (* Invoke a method through the parent class's vtable rather
           than through the 'this' vtable.
             - unlike with dynamic dispatch the 'super' class is known
               statically -- it is the parent of the type of the 'this' 
               variable.
             - you can manufacture a pointer to the appropriate method
               directly, without emitting LLVM code to lookup the method
             - the cmp_invocation helper can be used here                     *)
        | [{elt=Field({elt="super"});ext=sup}] ->
          (* An invocation of the super class' method. *)
          let _, (arg_typs, ret_typ) = Tctxt.lookup_method h sup f.elt in
          let cname = 
            begin match sup with
            | {elt=TRef {elt=RClass cid}} -> cid
            | _ -> failwith "cmp_call: couldn't get super name"
            end in
          let uid,this_typ = lookup_local "this" c in
          let fname = method_name cname.elt f.elt in
          let args = (ast_this_var this_typ)::es in
          let ftyp = (sup::arg_typs), ret_typ in
          cmp_invocation h c (Gid fname) args ftyp

        (* method invocation ------------------------------------------------ *)
        (* Implements dynamic dispatch.
           Due to the typechecker, the prefix path p will denote a valid
           object that can support the method f.  The code you generate should:
           - compile p as a path expression
           - use the object's vtbl pointer to find the function pointer
             for the method name f
           - compile the arguments to the method, including an instantiation of
             'this' to the object itself
           - call the method via the function pointer

           - the cmp_invocation function probably *won't* be of much use here,
             because there's no good "source" argument for the 'this' pointer
             but you might get some ideas of how to compile arguments and calls
             from that code.
           
           NOTE: much of the difficulty in this dynamic dispatch is understanding
           the types involved.  You will likely need to use bitcast on the
           object pointer (if, for example, the method being invoked is 
           inherited and thus expects a 'this' argument of a different type). *)
        | p -> (* Must be a method invocation of the form p.m(es)  *)
          let m_ty, obj_op, obj_path_str = cmp_path_exp h c p in
          let obj_llty = cmp_typ m_ty in
          let m_status, (arg_typs, ret_typ) = Tctxt.lookup_method h m_ty f.elt in
          let args, args_str = cmp_args h c es arg_typs in
          let obj_name =
            (match m_ty.elt with
              | TRef {elt=(RClass {elt=cid})} -> cid
              | _ -> failwith "cmp_call: cannot get class name"
            ) in
          let tgt_cid = 
            begin match m_status with
              | Tctxt.Extended
              | Tctxt.Overridden ->
                ( match m_ty with
                  | {elt=TRef {elt=(RClass {elt=cid})} } -> cid 
                  | _ -> failwith "cmp_call: not a class type"
                )
              | Tctxt.Inherited super_class -> super_class 
            end in 
          let arg_lltys, ret_llty = cmp_ftyp (arg_typs, ret_typ) in
          let tgt_llty = Ptr(object_named_ty tgt_cid) in
          let arg_lltys = tgt_llty::arg_lltys in
          let vptr_sym = gensym "vptr" in
          let vt_sym = gensym "vtable" in
          let mptr_sym = gensym "mptr" in
          let mth_sym = gensym "mth" in
          let thiscast_sym = gensym "thiscast" in
          let mth_gep = gep_for_method h (no_loc obj_name) f in
          let retsym = gensym "callret" in 
          let op = Id retsym in
          let args = (tgt_llty,Id thiscast_sym)::args in
          let stream = 
            obj_path_str >@
            [I(vptr_sym, Gep(obj_llty, obj_op, gep_vtbl_ptr))] >@
            [I(vt_sym, Load(Ptr(Ptr (class_named_ty obj_name)), Id vptr_sym))] >@
            [I(mptr_sym, Gep(Ptr (class_named_ty obj_name), Id vt_sym, mth_gep))] >@
            [I(mth_sym, Load(Ptr(Ptr(Fun (arg_lltys,ret_llty))), Id mptr_sym))] >@
            args_str >@
            [I(thiscast_sym, Bitcast(obj_llty,obj_op,tgt_llty))] >@
            [I(retsym, Call(ret_llty, (Id mth_sym), args))]
          in
          (ret_typ, op, stream)
      end
    | _ -> failwith "Impossible: Compiler Error"
  end

(* Compile a path as an expression ------------------------------------------ *)

(* Assumes p is a valid path expression, meaning that it is either:
    -  a path ending in a call to a non-void function
    -  or, a non-empty path that is valid as a left-hand-side, from which 
       a value can be loaded.                                                 *)
and cmp_path h (c:ctxt) (p:t path) : Ast.rtyp * Ll.operand * stream =
  let prefix, acc = prefix_of p in
  begin match acc.elt with
    | Call(f, es) -> cmp_call h c prefix acc 
    | _ ->
      let t, op, code = cmp_path_lhs h c p in
      let ptr_ty = Ptr (cmp_typ t) in
      let res_id = gensym "val_" in
      (Some t), (Id res_id), code >@ [I(res_id, Load(ptr_ty, op))]
  end  

and cmp_path_exp h (c:ctxt) (p:t path) : Ast.typ * Ll.operand * stream =
  let rt, op, p = cmp_path h c p in
  match rt with
  | None -> failwith "Compiler Error: should have been caught by TC"
  | Some t -> t, op, p
  
(* compile a statement ------------------------------------------------------ *)

(* Checks that the stmt is well typed and returns a new context and 
   a stream of LL instructions that implement the statment's behavior.

   - If the statement is a Return statement, it's form must match the
     rt argument.

   - If the statement is an SCall, it must be to a path identifying a 
     void function.  Note that this implies that the path has only one
     accessor.                                                                *)
and cmp_stmt h (c:ctxt) (rt:rtyp) (stmt : t Ast.stmt) : ctxt * stream =
  match stmt.elt with
  | Ast.Decl {elt= {ty; id; init}} ->
    let src_ty, init_op, init_code = cmp_exp h c init in
    let dst_ty = cmp_typ ty in
    let op, bitcast_code = bitcast_if_needed src_ty dst_ty init_op in
    (* Invariant: the context maps source variables to pointers *)
    let alloca_id = gensym id.elt in
    let c = add_local c id (alloca_id, ty) in
    (c,
     init_code >@
     [I(alloca_id, Alloca dst_ty)] >@
       bitcast_code >::
      I(""       , Store(dst_ty, op, Id alloca_id)))

  | Ast.Assn (path, e) ->
    let (path_ty, pop, path_code) = cmp_path_lhs h c path in
    let (src_ty, eop, exp_code) = cmp_exp h c e in
    let dst_ty = cmp_typ path_ty in
    let eop, bitcast_code = bitcast_if_needed src_ty dst_ty eop in
    c, (path_code >@ exp_code >@ bitcast_code >@ [I("", (Store (dst_ty, eop, pop)))])

  | Ast.If (guard, st1, st2) -> 
    let (guard_ty, guard_op, guard_code) = cmp_exp h c guard in
    let then_code = cmp_block h c rt st1 in
    let else_code = cmp_block h c rt st2 in
    let (lt, le, lm) = (gensym "then", gensym "else", gensym "merge") in
    c, (guard_code >:: T (Cbr (guard_op, lt, le)) >:: 
	L lt >@ then_code >:: T (Br lm) >:: 
        L le >@ else_code >:: T (Br lm) >::
        L lm)

  | Ast.While (guard, body) ->
    let (guard_ty, guard_op, guard_code) = cmp_exp h c guard in
    let (lcond, lbody, lpost) = gensym "cond", gensym "body", gensym "post" in
    let body_code = cmp_block h c rt body  in
    c, [T (Br lcond)] >:: L lcond >@ guard_code >::
        T (Cbr (guard_op, lbody, lpost)) >::
        L lbody >@ body_code >:: T (Br lcond) >::
        L lpost

  | Ast.For (inits, guard, after, body) ->
    let ast_bool b = ty ast_bool (Const(ty ast_bool (CBool b))) in
    let guard = match guard with Some e -> e | None -> (ast_bool true) in
    let after = match after with Some s -> [s] | None -> [] in
    let body = body @ after in
    let ds = List.map (fun d -> ty ast_null @@ Decl(d)) inits in
    let stream = cmp_block h c rt @@ ds @ [ty ast_null @@ Ast.While (guard, body)] in
                                     
    c, stream

  | Ast.Ret (eop) ->
    begin match eop, rt with
      | None, None ->    c, [T (Ret(Void, None))]

      | Some e, Some t ->
        let (src_ty, e_op, e_code) = cmp_exp h c e in
        let dst_ty = cmp_typ t in
        let op, bitcast_code = bitcast_if_needed src_ty dst_ty e_op in
        c, e_code >@ bitcast_code >@ [T (Ret(dst_ty, Some op))]

      | _ -> failwith "compiler error: incompatible return type"
    end

  | Ast.SCall path ->
    let _, _, code = cmp_path h c path in
    c, code

  (* dynamic cast ----------------------------------------------------------- *)
   (* Checks whether the dynamic type of e is a subtype of ty and, if so
      jumps to st1 (after extending the context with a new variable) or to
      st2.

      - NOTE: you can cast a vtable pointer to I8** and then load through it
        to find the superclass vtable.
      - the loop you generate to crawl up the class hierarchy will need
        to treat 'Object' specially (it's a termination condition of the 
        loop)
      - you will need to use Alloca to create storage for the new variable
        in the st1 branch (HINT: don't forget to extend the context!)
      - the st1 branch will also need a bitcast
      - much of the trickiness of this code is in generating code to
        handle the cases in a compact way:

     Cases:  
      ty is null:  static type of e is C? for some C
          -  if e == null branch to st1 else st2
      ty is t[] or string: static type of e is t[]? or string?
          -  if e == null branch to st2 else st1
      ty is C:     static type of e is D or D? for some D
          -  if e == null branch to st2, else 
          -  if e <> null crawl up vtbls looking for C
      ty is C?:    static type of e is D? for some D
          -  if e == null branch to st1, else 
          -  if e <> null crawl up vtbls looking for C

      - Note: I8* is a 'compatible' type for all of these comparisons.         *)
  | Ast.Cast(ty, id, e, st1, st2) ->
    (****The stream is probably not correct: it may need to compile id****)
    assert (ty <> e.ext);
    Tctxt.assert_typ_subtype h ty e.ext;
    try lookup_local id.elt c; failwith "variable already in context"
    with Not_found ->
    let new_var = [I (gensym "x_var", Alloca(Ptr I8))] in
    begin match ty.elt with
      | TNull -> c, (if e.ext = (no_loc TNull) then
                  new_var >@ cmp_block h (add_local c id (id.elt, ty)) rt st1 
                else cmp_block h c rt st2)
      | TRef r ->
        begin match r.elt with
          | RString -> c, (if e.ext = (no_loc TNull) then
                        cmp_block h (c) rt st2
                        else
                        new_var >@ cmp_block h (c) rt st1)
          | RArray arr_type -> c, (if e.ext = (no_loc TNull) then
                        cmp_block h (c) rt st2
                        else
                        new_var >@ cmp_block h (add_local c id (id.elt, ty)) rt st1)
          | RClass class_id ->
            if e.ext = (no_loc TNull) then
                (c, new_var >@ cmp_block h (add_local c id (id.elt, ty)) rt st1)
            else

            failwith "vtable crawl unimplemented"
              (*Loop to crawl up vtbls looking for C*)
        end
      | TNRef r ->
        begin match r.elt with
          | RClass class_id ->
            if e.ext = (no_loc TNull) then
                (c, new_var >@ cmp_block h (add_local c id (id.elt, ty)) rt st1)
            else failwith "vtable crawl unimplemented"
              (*Loop to crawl up vtbls looking for C*)
          | _ -> failwith "unsure if this is valid case of downcast"
        end
      | _ -> failwith "cannot cast this type"
    end

(* compile a block ---------------------------------------------------------- *)
and cmp_block h (c:ctxt) (rt:rtyp) (stmts:t Ast.block) : stream =
  snd (List.fold_left
         (fun (c,code) s ->
            let c, stmt_code = cmp_stmt h c rt s in
            c, code >@ stmt_code) (c,[]) stmts)



(* Compile the arguments of a function, mapping them to alloca'd
   storage space.                                                             *)
let cmp_args (c:ctxt) (args: (typ * id) list ) :
  ctxt * stream * (Ll.ty * uid) list =
  List.fold_right
    (fun  (s_typ, s_id) (c,code,args) ->
       let ll_id = s_id.elt in
       let ll_ty = cmp_typ s_typ in
       
       (* alloca_id is the name of the stack slot for the argument *)
       let alloca_id = gensym s_id.elt in
       
       (* Invariant: the context maps source variables to pointers *)
       let slot = alloca_id in
       let c = add_local c s_id (slot, s_typ) in
         (c,
          [I(alloca_id, Alloca ll_ty)] >::  
	   I("", Store(ll_ty, Id ll_id, Id alloca_id)) >@ code,
           (ll_ty, ll_id) :: args)) args (c,[],[]) 


(* context translation types ------------------------------------------------ *)
type ll_tdecls  = (Ll.tid * Ll.ty) list
type ll_funs    = (Ll.gid * Ll.fdecl) list 
type ll_globals = (Ll.gid * Ll.gdecl) list

(* compile a function declaration ------------------------------------------- *)

(* compiles a source function declaration, producing a target function 
   declaration and a list of global declarations.

   - this function may assume that the supplied context c has an 
     empty local context

   - the target function entry block code translates the
     function arguments by placing them in alloca'ed stack slots and
     extending the local context accordingly

   - the returned control flow graph and hoisted globals should be 
     created by build_cfg                                                     *)
let cmp_fdecl h (c:ctxt) {elt={rtyp; name; args; body}} :
  (Ll.gid * Ll.fdecl) * ll_globals =
  let c, args_code, args = cmp_args c args in
  let block_code = cmp_block h c rtyp body in
  let ll_rty = cmp_rtyp rtyp in
  let fty = (List.map fst args, ll_rty) in
  let param = List.map snd args in 
  let code = (args_code >@ block_code) in
  let cfg, globals = build_cfg code in
  (name.elt, {fty; param; cfg}), globals

(* compile a field declaration ---------------------------------------------- *)
(* Creates the code for initializing the field slots of an object 
   during the constructor's evaluation.                                       *)  
let cmp_field h c cid obj_ptr {elt={id; ty; init}} =
  let ll_ty = cmp_typ ty in
  let field_ptr = gensym @@ Printf.sprintf "%s_%s" cid.elt id.elt in
  let e_ty, e_op, e_code = cmp_exp h c init in
  let e_op, bitcast_code = bitcast_if_needed e_ty ll_ty e_op in
  let gep_path = gep_for_field h cid id in
    e_code >@
    bitcast_code >@
    [I(field_ptr, Gep(Ptr(object_named_ty cid.elt), Id obj_ptr, gep_path))] >@
    [I("dummy", Store(ll_ty, e_op, Id field_ptr))]
  
let cmp_fields h c cid obj_ptr_id flds =
  List.map (cmp_field h c cid obj_ptr_id) (List.rev flds) |>
  List.flatten

(* compile a constructor ---------------------------------------------------- *)
(* Generate code that constructs an object of the class cid:

    1. Extend args list with "this" parameter
        - 'this' hasn't been initialized yet, so it's convenient
          to treat it as an i8*, which means the source type
          can be treated as being 'string'
        - the space for the object will be allocated by the
          'new' expression
     2. Invoke the superclass constructor passing in 'this' and sups as arguments
     3. Bitcast the pointer to the real class type
     4. Initialize the fields -- see the "cmp_fields" helper function
     5. Initialize the vtable pointer of the object                        
     6. Pack the control flow graph and appropriate type information into
        a global fdecl

  NOTE: constructors don't return any result -- the 'new' expression already
  has the pointer that would be returned from the constructor.  Therefore
  the ource "type" of the constructor 

  NOTE: the gid for the constructor can be found using the 'ctr_name' helper
  
  NOTE: you can look up the superclass information using 'lookup_interface'
*)
let cmp_ctr (h:Tctxt.hierarchy) (c:ctxt) (cid:id) (sup:id)
    ({elt={args; sups; flds}}:t ctr) :  (Ll.gid * Ll.fdecl) * ll_globals =
  let args = (ast_str, this_id)::args in
  let args_c, args_s, args_l = cmp_args c args in
  let sup_name = ctr_name sup.elt in
  let args_l2 = 
    List.map (fun (x,y) -> (x,Id y)) args_l in
  let this_sym = gensym "this" in
  let this_obj = gensym "thisobj" in
  let class_ty = cmp_typ (ast_class_typ cid) in
  let this_loc, this_ty = lookup_local this_id.elt args_c in
  let fields = cmp_fields h args_c cid this_sym flds in
  let args_sup, sup_s = 
    List.fold_left 
      (fun (a,s) x -> 
        let ty,op,st = cmp_exp h args_c x in
        ([(ty,op)] >@ a, st >@ s)) 
      ([((cmp_typ this_ty), Id this_obj)],[])
      sups in
  let vsym = gensym "vtbl" in
  let vname = vtbl_name cid.elt in
  let vtyp = Ptr (class_named_ty cid.elt) in

  let stream = 
    args_s >@ 
    [I(this_obj, Load(Ptr (cmp_typ this_ty), Id this_loc))] >@
    sup_s >@
    [I("", Call(Void, Gid sup_name, args_sup))] >@
    [I(this_sym, Bitcast(cmp_typ this_ty, Id this_obj, class_ty))] >@
    fields >@
    [I(vsym, Bitcast(class_ty, Id this_sym, Ptr vtyp))] >@
    [I("", Store(vtyp,Gid vname,Id vsym))] >@
    [T(Ret(Void,None))] in
  let cfg, ll_globals = build_cfg stream in
  let fdecl = {
    fty = (List.map fst args_l, Void);
    param = List.map snd args_l;
    cfg = cfg
  } in 
  let gid = ctr_name cid.elt in
  (gid, fdecl), ll_globals


let cmp_method h c cid sup {elt={rtyp; name; args; body}} =
  let n = method_name cid.elt name.elt in
  let args = (ast_class_typ cid, this_id)::args in
  cmp_fdecl h c (ty ast_null @@ {rtyp=rtyp; name=no_loc n; args; body})

let cmp_cdecl (h:Tctxt.hierarchy) (c:ctxt) {elt={cid;sup;ctr;methods}} :
  ll_funs * ll_globals =
  let ctr_fdecl, ctr_globals = cmp_ctr h c cid sup ctr in
  let method_fdecls, method_globals = List.split @@ List.map (cmp_method h c cid sup) methods in
  ctr_fdecl :: method_fdecls,
  ctr_globals @ (List.flatten method_globals)

(* compile all of the fdecls ------------------------------------------------ *)
let cmp_cfdecls (h:Tctxt.hierarchy) (c:ctxt) (p:t Ast.prog) :
  ll_funs * ll_globals =
  let rec loop p (fs, gs) =
    match p with
    | [] -> List.rev fs, List.rev gs

    | Ast.Gvdecl vd :: q -> loop q (fs, gs)

    | Ast.Gcdecl cd :: q ->
      let fdecls, globals = cmp_cdecl h c cd in
      loop q ((List.rev fdecls) @ fs, globals @ gs)

    | Ast.Gfdecl fd :: q ->
      let fdecl, globals = cmp_fdecl h c fd in
      loop q (fdecl :: fs, globals @ gs)
  in
  loop p ([], [])

(* compile a global initializer --------------------------------------------- *)

(* Invariant: ty is the source type of the global value.  init is a
   _constant_ expression.  Outputs the target type, which should be
   correspond to the ginit_value, and ll_globals that initialize the
   statically-allocated memory block correctly.

   Unlike constant expressions that appear inside of functions (which
   require dynamic allocation of storage space), globally defined
   constants should simply translate to a sequence of appropriate LL 
   global initializers.  

   - for Null, Bool, and Int types the result type is simply 
     (cmp_typ ty)
   
   - for String and Array types the resulting Ll.ty should correspond
     exactly to the ginit value's type, which may be more specific
     than (cmp_typ ty).  (Hint: the clang compiler's type errors
     can help you figure yout the exact types of the ginit values.)

   - global string declarations must translate to a global string
     constant, plus a reference to that constant.

   - global array declarations must include appropriate Oat-style
     array length information, and, like strings, must compile not
     only to the data, but to a pointer refering to that data.  The 
     static LL type of an array must use the correct length.  [See
     the corresponding note in cmp_path_lhs]                 

   - this function should fail if the initializer expression has
     incorrect type, or if the global initializer contains a
     non-constant expression.                                                 *)
let rec cmp_init (t:Ast.typ) (init:t Ast.exp) :  Ll.ty * Ll.ginit * ll_globals =
  let ll_ty = cmp_typ t in
  match init.elt, t.elt with
  | Const {elt=CNull}, _  -> ll_ty, GNull, []
  | Const {elt=CBool b}, TBool -> ll_ty, (if b then GInt 1L else GInt 0L), []
  | Const {elt=CInt i}, TInt   -> ll_ty, (GInt i), []

  | Const {elt=CStr s}, TRef {elt=RString} ->
    let gid = gensym "str_" in
    let ll_ty = str_arr_typ s in
    (Ptr ll_ty), (GGid gid), [(gid, (ll_ty, GString s))]

  | Const {elt=CArr cs}, TRef {elt=RArray u} ->
    let elts, code = List.fold_left
        (fun (elts, code) cst ->
           let ll_u, einit, ecode = cmp_init u (ty u (Const cst)) in
           elts @ [(ll_u, einit)], code @ ecode) ([], []) cs
    in
    let len = List.length cs in
    let ll_u = cmp_typ u in 
    let arr_ty = Struct [I64;Array(len, ll_u)] in
    let gid = gensym "arr_" in
    (Ptr arr_ty), (GGid gid),
    (gid, (arr_ty,
           GStruct [(I64, GInt (Int64.of_int len));
                    (Array(len, ll_u), GArray elts)]))::code
  | Const _, TNRef r -> cmp_init (no_loc @@ TRef r) init

  | _, _ -> failwith @@
    Printf.sprintf "cmp_init found ill-typed or non-constant global initializer: %s %s"
      (Astlib.string_of_exp init) (Range.string_of_range init.loc)


(* compile the global context ----------------------------------------------- *)

(* compiles a source global declaration into a global context entry and 
   a sequence of LL globals                                                   *)
let gvdecl_typ {elt={ty; id; init}} : (id * global_binding) * ll_globals =
  let ll_ty, ginit, gs  = cmp_init ty init in
  (id, (id.elt, ty, ll_ty)), (id.elt, (ll_ty, ginit))::gs


(* compiles a source function type declaration into a function context entry  *)
let fdecl_typ {elt={rtyp; name; args}} : id * funs_binding =
  let ts = List.map fst args in
  (name, (name.elt, (ts,rtyp)))

(* produces the top-level global context suitable for typechecking/compiling
   each function declaration, as well as the globals needed to initialize
   global data declarations                                                   

   Oat programs consist of a sequence of global declarations
   containing data values and (possibly) mutually recursive function
   definitions.  Therefore, to typecheck a function body, it is
   necessary to first figure out the global context, which has the
   type information about all of the declarations.  

   Use gvdecl_typ and gfdecl_typ to complete this function.                   *)
let cmp_global_ctxt (p:t Ast.prog) (c:ctxt) : ctxt * ll_globals =
  List.fold_left
    (fun (c, glbls) ->
       (function
         | Ast.Gvdecl g ->
           let (id, bnd), gs = gvdecl_typ g in
           (add_global c id bnd, gs @ glbls)
           
         | Ast.Gfdecl f ->
           let (id, bnd) = fdecl_typ f in
           (add_function c id bnd, glbls)

         | Ast.Gcdecl cd ->
           (c, glbls)
       ))
    (c, []) p


(* compile the class hierarchy ---------------------------------------------- *)
(* For each class C in the hierrarchy produce:
     - a type for C's vtable  
     - the global initializers for that vtable
     - an object type named C (see object_ty)                                 *)
let cmp_hierarchy (h:Tctxt.hierarchy) : ll_tdecls * ll_globals =
  List.fold_left
    (fun (ts, gs) (cls, iface) ->
       let vname = vtbl_name cls in
       let vtyp  = class_named_ty cls in
       let objt  = object_ty cls iface in
       let (tid, vtbl_struct_ty), vtbl =
         if cls = "Object" then 
           (class_struct_name "Object", Struct []), (GStruct [])
         else
           class_to_vtbl cls iface
       in
       objt::(tid, vtbl_struct_ty)::ts,
       (vname, (vtyp, vtbl))::gs
    )
    ([], [])
    h

(* Oat initial context ------------------------------------------------------ *)

let init_ctxt =
  List.fold_left
    (fun c (s, fty) -> add_function c (no_loc s) (s,fty)) empty_ctxt 
    Tc.prelude


(* Compile a top-level program ---------------------------------------------- *)
let cmp_prog (h:Tctxt.hierarchy) (p: t Ast.prog) : Ll.prog =
  let tdecls, glbls_h = cmp_hierarchy h in
  let fdecl_obj = (ctr_name "Object",
                   {fty=([Ptr I8], Void); param=["o"];
                    cfg={insns=[]; terminator=Ret(Void, None)}, []})
  in
  let c, gdecls = cmp_global_ctxt p init_ctxt in
  let (fdecls, hoisted_globals) = cmp_cfdecls h c p  in
  { tdecls; gdecls=glbls_h @ gdecls @ hoisted_globals;  fdecls=fdecl_obj::fdecls; }



(* Oat LLVM prelude --------------------------------------------------------- *)

(* This is a string represeting the LLVM IR external declarations for
   the oat built-in functions.  These functions are implemented in
   runtime.c                                                                  *)
let oat_ll_prelude =
  let to_str (fn, (args, rtyp)) =
    let args_str = List.map (fun t -> string_of_ty (cmp_typ t)) args
                   |> String.concat ", "
    in
    let rtyp_str = string_of_ty (cmp_rtyp rtyp) in
    Printf.sprintf "declare %s @%s (%s)"
      rtyp_str fn args_str
  in
  let declares = List.map to_str Tc.prelude
               |> String.concat "\n"
  in
    
  Printf.sprintf 
  "target datalayout = \"e-m:o-i64:64-f80:128-n8:16:32:64-S128\"\n\n\
  ; ------------------------------------------------ prelude\n\n\
  ; internal oat functions (not available in source)\n\
  declare i8* @oat_malloc(i64)\n\
  declare {i64, [0 x i64]}* @oat_alloc_array (i64)\n\
  \n\
  ; oat 'builtin' functions\n\
  %s\n\
  %s\n\
  ; --------------------------------------------------------\n\n\
  " declares ""

    
