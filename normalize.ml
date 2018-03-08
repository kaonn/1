open Core.Std
open Printf
open Typedtree

exception Fail of string
exception Eval of string

let count = ref 0

let new_name () = let _ = inc count in "x" ^ (Int.to_string !count) 

let foldi_right = fun l i f -> 
  let indexed = List.map l (fun i a -> i, a) in 
  foldi_right indexed (i,0) f
  
let rec normalize : expression -> expression = 

module NormArg : TypedtreeMap.MapArgument = struct 
include TypedtreeMap.DefaultMapArgument

let enter_expression =
fun e -> match e.exp_desc with
| Texp_ident _ -> e
| Texp_constant _ -> e
| Texp_let _ -> e
| Texp_function _ -> e
| Texp_apply (f, ls) -> 
  let es = List.map ls (fun (_,eo,_) -> match eo with Some arg -> arg | _ => raise (Eval "labeled arguments not supported")) in
  let fname = new_name () in 
  let args = List.map es (fun _ -> new_name ()) in
  let apps = List.map es (fun _ -> new_name ()) in
  let res = List.last_exn apps in
  let names = List.zip_exn args apps
  let eapp = List.foldi_right names ~init:res  (fun c (xi, fi) ->
  )
    let List.foldl es ~init:
  
  
  
| Texp_match of expression * case list * case list * partial
| Texp_try of expression * case list
| Texp_tuple of expression list
| Texp_construct of
    Longident.t loc * constructor_description * expression list
| Texp_variant of label * expression option
| Texp_record of
    (Longident.t loc * label_description * expression) list *
      expression option
| Texp_field of expression * Longident.t loc * label_description
| Texp_setfield of
    expression * Longident.t loc * label_description * expression
| Texp_array of expression list
| Texp_ifthenelse of expression * expression * expression option
| Texp_sequence of expression * expression
| Texp_while of expression * expression
| Texp_for of
    Ident.t * Parsetree.pattern * expression * expression * direction_flag *
      expression
| Texp_send of expression * meth * expression option
| Texp_new of Path.t * Longident.t loc * Types.class_declaration
| Texp_instvar of Path.t * Path.t * string loc
| Texp_setinstvar of Path.t * Path.t * string loc * expression
| Texp_override of Path.t * (Path.t * string loc * expression) list
| Texp_letmodule of Ident.t * string loc * module_expr * expression
| Texp_assert of expression
| Texp_lazy of expression
| Texp_object of class_structure * string list
| Texp_pack of module_expr

end
