open Assert
open Gradedtests

(* These tests are provided by you -- they will be graded manually *)

(* You should also add additional test cases here to help you   *)
(* debug your program.                                          *)
let orchestra_output : string =
  "Squak! Ssshhhp. Tap.\n" ^
  "Squak! Ssshhhp. Tap.\n" ^
  "Squak! Ssshhhp. Tap.\n" ^
  "Squak! Ssshhhp. Tap.\n" ^
  "Squak! Ssshhhp. Tap.\n" ^
  "Squak! Ssshhhp. Tap.\n" ^
  "Squak! Ssshhhp. Tap.\n" ^
  "Squak! Ssshhhp. Tap.\n" ^
  "Squak! Ssshhhp. Tap.\n" ^
  "Squak! Ssshhhp. Tap.\n" ^
  "Splat! \n" ^
  "Splat! \n" ^
  "Splat! \n" ^
  "Splat! \n" ^
  "Splat! \n" ^
  "Splat! \n" ^
  "Splat! \n" ^
  "Splat! \n" ^
  "Splat! \n" ^
  "Splat! \n" ^
  "Splat! \n" ^
  "Splat! \n" ^
  "Splat! \n" ^
  "Splat! \n" ^
  "\n" ^
  "Fffffff. Fffffff. Fffffff. Fffffff. Fffffff. Fffffff. Fffffff. Fffffff. " ^ 
  "Fffffff. Fffffff. Fffffff. Fffffff. Fffffff. Fffffff. 0"

let fizz_buzz_output : string = "12Fizz4BuzzFizz78FizzBuzz11Fizz1314Fizzbuzz1617Fizz19Buzz0"

let student_tests = [
  "oatprograms/pqueue.oat", "12";
  "oatprograms/orchestra.oat", orchestra_output;
  "oatprograms/enterprise_quality_fizz_buzz.oat", fizz_buzz_output;
  "oatprograms/fold.oat", "45";
  "oatprograms/linkedlist.oat", "1230"
]

let provided_tests : suite = [
  GradedTest("student tests", 0, executed_oat_file student_tests)
] 
