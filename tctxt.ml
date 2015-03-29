open Ast

exception TypeError of string

let tc_error s =
  raise @@ TypeError s

(* typechecking context ----------------------------------------------------- *)

(* Each part of the context is just a mapping from source identifiers
   (represented as strings) to their source types.  Each map
   is just an association list.

   - the funs field keeps track of globally declared functions

   - the global field keeps track of other global identifiers.

   - the local field maps source local variables to their
     corresponding target uid's and (source) types.                           *)
type funs_binding   = Ast.ftyp
type global_binding = Ast.typ
type local_binding  = Ast.typ

type ctxt = {
  funs    : (string * funs_binding)   list;   (* Functions scope *)
  global  : (string * global_binding) list;   (* Global scope *)
  local   : (string * local_binding)  list;   (* Local scope  *)
}
let empty_ctxt = { funs   = []; global = []; local  = []; }

(* Information about a method's relation to the class hierchy                 *)
type status =
  | Extended
  | Overridden
  | Inherited of string

(* Oat class interfaces ----------------------------------------------------- *)

(* - constructors are considered to have 'void' return type
   - the ftyp of methods does not include the implicit 'this' parameter       *)
type interface = {
  sup : id
; ctr : ftyp
; flds : (string * typ) list
; mths : (string * (status * ftyp)) list
}
type hierarchy = (string * interface) list      (* class hierarchy *)


(* extending the context ---------------------------------------------------- *)

(* these add functions check to make sure that the identifier isn't already 
   bound in the context.                                                      *)
let add_function (c:ctxt) (id:id) bnd : ctxt =
  if List.mem_assoc id.elt c.funs then
    tc_error @@ Printf.sprintf "Function %s already defined. %s" id.elt
      (Range.string_of_range id.loc)
  else {c with funs = (id.elt, bnd)::c.funs}

let add_global (c:ctxt) (id:id) bnd : ctxt =
  if List.mem_assoc id.elt c.global then
    tc_error @@ Printf.sprintf "Global %s already defined. %s" id.elt
      (Range.string_of_range id.loc)
  else {c with global = (id.elt, bnd)::c.global}

let add_local (c:ctxt) (id:id) bnd : ctxt =
  if List.mem_assoc id.elt c.local then
    tc_error @@ Printf.sprintf "Local %s already defined. %s" id.elt
      (Range.string_of_range id.loc)
  else {c with local = (id.elt,bnd)::c.local}

(* looking up a binding in the context -------------------------------------- *)

(* these functions raise the exception Not_found if there is no binding 
   for the identifier present in the context                                  *)

let lookup_function (id:string) (c:ctxt) : Ast.ftyp =
  List.assoc id c.funs

let lookup_local (id:string) (c:ctxt) : Ast.typ =
  List.assoc id c.local

let lookup_global (id:string) (c:ctxt) : Ast.typ =
  List.assoc id c.global

(* hierarchy functions ------------------------------------------------------ *)
let lookup_interface (id:string) (h:hierarchy) : interface =
  List.assoc id h

let add_interface (h:hierarchy) (id:id) (i:interface) : hierarchy =
  if List.mem_assoc id.elt h then
    tc_error @@ Printf.sprintf "Class %s already defined. %s" id.elt
      (Range.string_of_range id.loc)
  else (id.elt, i)::h
    

(* subtyping ---------------------------------------------------------------- *)

(* returns true if C1 <:* C2 in the class hierarchy                           *)
let rec extends (h:hierarchy) (c1:cid) (c2:cid) : bool =
failwith "HW5: extends not implemented"


(* join --------------------------------------------------------------------- *)
(* - compute the least upper bound of u and t according to the subtype
     relation <: defined in the Oat reference

   - if there is no upper bound of u and t, return None

   HINT: you will probably want a helper function defined mutually-recursively
   with this one

   NOTE: you will probably want to use the [no_loc] helper function to
   help construct the returned typ values.                                    *)
let rec join_typ (h:hierarchy) (u:typ) (t:typ) : typ option =
  failwith "HW5: join_typ not implemented"

(* lift the 'join' operation to a set of types ------------------------------ *)
(* NOTE: monads would be nice here... :-)                                     *)
let join_typs (h:hierarchy) (ts:typ list) : typ option =
  begin match ts with
    | [] -> None
    | t::ts -> List.fold_left
                 (fun u t ->
                    match u with
                    | None -> None
                    | Some v -> join_typ h v t) (Some t) ts
  end

(* check that t is a subtype of u ------------------------------------------- *)
let assert_typ_subtype (h:hierarchy) (t:typ) (u:typ) : unit =
  begin match join_typ h t u with
    | Some v when (Astlib.eq_typ u v) -> ()
    | _ -> tc_error @@ Printf.sprintf "expected subtype: %s <: %s did not hold"
        (Astlib.string_of_typ t)
        (Astlib.string_of_typ u)
  end

(* check that the type of an expression is a subtype of u ------------------- *)
(* We define this function, even though it's redundant with assert_typ_subtype
   because it can give slightly more informative error messages.              *)  
let assert_exp_subtype (h:hierarchy) (e: typ Ast.exp) (u:typ) : unit =
  begin match join_typ h e.ext u with
    | Some v when (Astlib.eq_typ u v) -> ()
      
    | _ -> tc_error @@
      Printf.sprintf "expression %s has type %s but type %s was expected %s"
        (Astlib.string_of_exp e)
        (Astlib.string_of_typ e.ext)
        (Astlib.string_of_typ u)
        (Range.string_of_range e.loc)
  end

(* function subtyping ------------------------------------------------------- *)
(* recall that:
    - output types are _covariant_
    - input types are _contravariant_                                         *)  
let assert_sub_ftyp (h:hierarchy) (ts, r) (us, s) : unit =
  begin match r, s with
    | None, None -> ()
    | Some t, Some u -> assert_typ_subtype h t u
    | _, _ -> tc_error @@ Printf.sprintf "return types disagree"
  end;
  try
    List.iter2 (fun t u -> assert_typ_subtype h u t) ts us
  with
    Invalid_argument _ ->
    tc_error @@ Printf.sprintf "functions %s and %s have different arities"
      (Astlib.string_of_ftyp (ts, r))
      (Astlib.string_of_ftyp (us, s))




(* get the type of a constructor for a class -------------------------------- *)
(* fails if c isn't in the class hierarchy *)
let lookup_ctr_ftyp (h:hierarchy) (cls:string) : ftyp =
  if cls = "Object" then ([], None)
  else
    (List.assoc cls h).ctr


(* find a field signature given a type -------------------------------------- *)
(* fails if t is not a reference to a class                                   *)
let rec lookup_field (h:hierarchy) (t:typ) (fld:string) : Ast.typ =
  begin match t.elt with
    | TRef {elt=RClass(cid)} ->
      begin let iface = lookup_interface cid.elt h in
      try
        List.assoc fld iface.flds
      with
      | Not_found -> lookup_field h (ast_class_typ iface.sup) fld
      end
    | _ -> tc_error @@ Printf.sprintf "type %s has no fields %s"
             (Astlib.string_of_typ t)
             (Range.string_of_range t.loc)
  end

(* find a method signature given a type ------------------------------------- *)
(* fails if t is not a reference to a class                                   *)
let rec lookup_method (h:hierarchy) (t:typ) (mth:string) : status * Ast.ftyp =
  begin match t.elt with
    | TRef {elt=RClass(cid)} ->
      begin let iface = lookup_interface cid.elt h in
      try
        List.assoc mth iface.mths
      with
      | Not_found -> lookup_method h (ast_class_typ iface.sup) mth
      end
    | _ -> tc_error @@ Printf.sprintf "type %s has no methods %s"
             (Astlib.string_of_typ t)
             (Range.string_of_range t.loc)
  end
  

(* helper functions for printing -------------------------------------------- *)
let string_of_status = function
  | Extended   -> "extended"
  | Inherited s -> Printf.sprintf "inherited from %s" s
  | Overridden -> "overridden"

let string_of_interface {sup; ctr; flds; mths} =
  Printf.sprintf "<: %s {\n  ctr: %s\n  flds:\n%s\n  mths:\n%s\n}\n"
    sup.elt
    (Astlib.string_of_ftyp ctr)
    (String.concat "\n  " (List.map (fun (x,t) ->
         Printf.sprintf "%s %s;" (Astlib.string_of_typ t) x) flds))
    (String.concat "\n  " (List.map (fun (x,(s,t)) ->
         Printf.sprintf "%s : %s (%s);"
           (Astlib.string_of_ftyp t) x (string_of_status s)) mths))

let string_of_hierarchy (h:hierarchy) =
  String.concat "\n\n" (List.map (fun (c, i) ->
      Printf.sprintf "%s %s" c (string_of_interface i)) h)

let string_of_ctxt (c:ctxt) =
  let funs = String.concat "\n" (List.map (fun (s,ftyp) ->
      Printf.sprintf "  %s : %s" s (Astlib.string_of_ftyp ftyp)) c.funs)  in

  let global = String.concat "\n" (List.map (fun (s,typ) ->
      Printf.sprintf "  %s : %s" s (Astlib.string_of_typ typ)) c.global)  in

  let local =  String.concat "\n" (List.map (fun (s,typ) ->
      Printf.sprintf "  %s : %s" s (Astlib.string_of_typ typ)) c.local) in

  Printf.sprintf "funs:\n%s\nglobal:\n%s\nlocal:\n%s\n%!" funs global local
