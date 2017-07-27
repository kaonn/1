open Core.Std
open Printf
open Typedtree

exception Fail of string
exception Eval of string

module H = Map.Make(Int)
module V = Map.Make(String)
module R = Set.Make(Int)
module F = Set.Make(Int)
module Var = Set.Make(String)

type loc = int
type value = Nat of int * loc | T of loc | F of loc | Null of loc | Loc of loc * loc | Pair of value * value * loc

type context = {m : int; st : value V.t; hp : value H.t; r : R.t; f : F.t}

let heap_start = ref 0
let new_loc : unit -> loc =
  fun _ ->
  let l = !heap_start in
  incr heap_start; l

let rec val_tostring : value -> string =
  function (Nat (i, l)) -> (Int.to_string i) ^ "@" ^ (Int.to_string l)
  | T l -> "T@" ^ Int.to_string l
  | F l -> "F@" ^ Int.to_string l
  | Null l -> "Null@"  ^Int.to_string l
  | Loc (l1,l2)  -> "L:" ^ (Int.to_string l1) ^ "@" ^ (Int.to_string l2)
  | Pair (v1,v2,l) -> "<" ^ (val_tostring v1) ^ ", " ^ (val_tostring v2) ^ ">@" ^ Int.to_string l

let st_tostring : value V.t -> string =
  fun st ->
  List.fold_right (List.map (V.to_alist st) (fun (x,v) -> x ^ " -> " ^ val_tostring v ^ ", ")) ~init:"" ~f:(fun a b -> a^b)

let rec subst : Typedtree.expression -> Path.t -> Typedtree.expression -> Typedtree.expression =
    fun p1 p2 exp -> match exp.Typedtree.exp_desc with
    | Typedtree.Texp_ident (path, loc, val_desc) ->
      if Path.same p2 path then {exp with Typedtree.exp_desc = p1.Typedtree.exp_desc}
      else exp
    | Typedtree.Texp_constant _ -> exp
    | Typedtree.Texp_let (rflag, pairs, e) ->
      let undef, def = List.split_while pairs ~f:(fun (p,_) ->
        let bound_list = List.map (Typedtree.pat_bound_idents p) (fun (ident,_) -> Path.Pident ident ) in
           List.exists bound_list (Fn.compose not (Path.same p2))
        || List.is_empty bound_list
        ) in
      let undef' = List.map undef (fun (p,e) -> p, subst p1 p2 e) in
      let def', e' =
        match def with
        | [] -> [], subst p1 p2 e
        | (pi,ei)::xs -> (pi, subst p1 p2 ei)::xs, e
      in {exp with Typedtree.exp_desc = Typedtree.Texp_let (rflag, undef' @ def', e')}

    | Typedtree.Texp_function (label, pairs, part) ->
      let pairs' = List.map pairs (fun (p,e) ->
        let bound_list = List.map (Typedtree.pat_bound_idents p) (fun (ident,_) -> Path.Pident ident) in
        if List.exists bound_list (Path.same p2) then (p,e)
        else (p, subst p1 p2 e)
      ) in
      {exp with Typedtree.exp_desc = Typedtree.Texp_function (label, pairs', part)}

    | Typedtree.Texp_apply (e, es) ->
      let es' = List.map es (fun (l,e,o) ->
        match e with
        | Some e' -> (l, Some (subst p1 p2 e'), o)
        | _ -> (l,e,o)
      ) in
      {exp with Typedtree.exp_desc = Typedtree.Texp_apply (subst p1 p2 e, es')}

    | Typedtree.Texp_match (e, pairs, part) ->
      let e' = subst p1 p2 e in
      let pairs' = List.map pairs (fun (p,e) ->
        let bound_list = List.map (Typedtree.pat_bound_idents p) (fun (ident,_) -> Path.Pident ident) in
        if List.exists bound_list (Path.same p2) then (p, e)
        else (p, subst p1 p2 e)
    ) in
      {exp with Typedtree.exp_desc = Typedtree.Texp_match (e', pairs', part)}

    | Typedtree.Texp_try (e, pairs) ->
      let e' = subst p1 p2 e in
      let pairs' = List.map pairs (fun (p,e) ->
        let bound_list = List.map (Typedtree.pat_bound_idents p) (fun (ident,_) -> Path.Pident ident) in
        if List.exists bound_list (Path.same p2) then (p,e)
        else (p, subst p1 p2 e)
      ) in
      {exp with Typedtree.exp_desc = Typedtree.Texp_try (e', pairs')}

    | Typedtree.Texp_tuple es ->
      let es' = List.map es (subst p1 p2) in
      {exp with Typedtree.exp_desc = Typedtree.Texp_tuple es'}

    | Typedtree.Texp_construct (loc, desc, es, b) ->
      let es' = List.map es (subst p1 p2) in
      {exp with Typedtree.exp_desc = Typedtree.Texp_construct (loc, desc, es', b)}

    | Typedtree.Texp_ifthenelse (e1, e2, e3) ->
    {exp with Typedtree.exp_desc = Typedtree.Texp_ifthenelse (subst p1 p2 e1, subst p1 p2 e2, Option.map e3 (subst p1 p2))}

    | Typedtree.Texp_sequence (e1, e2) ->
    {exp with Typedtree.exp_desc = Typedtree.Texp_sequence (subst p1 p2 e1, subst p1 p2 e2)}

    | _ -> raise (Fail "unsupported substitutions")

let bound_set = ref Var.empty
let free_set = ref Var.empty

module IterTree = TypedtreeIter.MakeIterator(
  struct
    include TypedtreeIter.DefaultIteratorArgument

    let enter_expression e =
      match e.exp_desc with
      | Texp_ident (path,_,_) ->
        if not(Var.mem !bound_set (Path.name path))
        then free_set := Var.add !free_set (Path.name path)
        else ()
      | Texp_let (_, pes,e2) ->
        List.iter pes (fun ({pat_desc = Tpat_var (ident,_)},e) -> bound_set := Var.add !bound_set (Path.name (Path.Pident ident)))
      | Texp_function (_,[{pat_desc = Tpat_var (ident,_)},e],_) ->  bound_set := Var.add !bound_set (Path.name (Path.Pident ident))
      | _ -> ()


    let leave_expression e =
      match e.exp_desc with
      | Texp_let (_, pes,e2) ->
      List.iter pes (fun ({pat_desc = Tpat_var (ident,_)},e) -> bound_set := Var.remove !bound_set (Path.name (Path.Pident ident)))
      | Texp_function (_,[{pat_desc = Tpat_var (ident,_)},e],_) ->  bound_set := Var.remove !bound_set (Path.name (Path.Pident ident))
      | _ -> ()

  end
  )

  let mk_exp : Env.t -> Typedtree.expression_desc -> Types.type_expr -> expression =
      fun env desc t ->
      { Typedtree.exp_desc = desc;
        Typedtree.exp_loc = Location.none;
        Typedtree.exp_extra = [];
        Typedtree.exp_type = t;
        Typedtree.exp_env = env}

    let mk_exp_var : Env.t -> Path.t -> Types.type_expr -> Typedtree.expression =
      fun env path t ->
        let val_desc =
        {
          Types.val_type = t;
          Types.val_kind = Types.Val_reg;
          Types.val_loc = Location.none;
        } in
        let desc = Typedtree.Texp_ident (path, Location.mknoloc (Longident.Lident ""), val_desc) in
        mk_exp env desc t

    let mk_pat : Env.t -> Typedtree.pattern_desc -> Types.type_expr -> Typedtree.pattern =
      fun env desc t ->
        { Typedtree.pat_desc = desc;
          Typedtree.pat_loc = Location.none;
          Typedtree.pat_extra = [];
          Typedtree.pat_type = t;
          Typedtree.pat_env = env}

(* let fv e =
  let _ = free_set := Var.empty in
  let _ = free_set := Var.empty in
  let _ = IterTree.iter_expression e in
  !free_set *)

let fv exp =

  let bound_names p = List.map (pat_bound_idents p) (fun (ident,_) -> Path.name (Path.Pident ident)) in

  let rec traverse bound_set exp =
    match exp.exp_desc with
    | Texp_ident (path,_,_) ->
      if Var.mem bound_set (Path.name path) then Var.empty else Var.singleton (Path.name path)
    | Texp_constant _ -> Var.empty
    | Texp_let (_,[],e) -> traverse bound_set e
    | Texp_let (rflag,(p,e)::xs,e1) ->
      let f1 = traverse bound_set e in
      let e' = {exp with exp_desc = Texp_let (rflag,xs,e1)} in
      let bound_vars = bound_names p in
      let f2 = traverse (Var.union bound_set (Var.of_list bound_vars)) e' in
      Var.union f1 f2

    | Texp_function (_,pes,_) -> List.map pes (fun (p,e) -> traverse (Var.union bound_set (p |> bound_names |> Var.of_list)) e) |> Var.union_list

    | Texp_apply (e,es) ->
      let f1 = traverse bound_set e in
      let f2 = List.map es (fun (_,eo,_) -> match eo with Some e' -> traverse bound_set e' | _ -> Var.empty) |> Var.union_list in
      Var.union f1 f2

    | Texp_match (e,pes,_) ->
      let f1 = traverse bound_set e in
      let f2 = List.map pes (fun (p,e) -> traverse (Var.union bound_set (p |> bound_names |> Var.of_list)) e)  |> Var.union_list in
      Var.union f1 f2

    | Texp_tuple es -> List.map es (traverse bound_set) |> Var.union_list

    | Texp_construct (_,_,es,_) -> List.map es (traverse bound_set) |> Var.union_list

  in
  traverse Var.empty exp


let rec reach : context -> value -> R.t =
  fun ctx -> function
  | Nat (_,l)
  | T l
  | F l
  | Null l -> R.singleton l
  | Loc (l1,l2) ->
    (match H.find ctx.hp l1 with
    | Some v -> R.add (reach ctx v) l2
    | _ -> raise (Fail "malformed heap"))
  | Pair (v1,v2,l) ->
    R.add (R.union (reach ctx v1) (reach ctx v2)) l

let rec hold : context -> R.t -> R.t =
  fun ctx r ->
    R.fold_right r ~init:R.empty ~f:(fun l acc ->
      match H.find ctx.hp l with
      | Some v -> R.union acc (R.add (reach ctx v) l)
      | _ -> raise (Fail "malformed heap")
    )

let locs : context -> expression -> R.t =
  fun ctx e ->
    let free = fv e in
    Var.fold_right free ~init:R.empty ~f:(fun s acc ->
      match V.find ctx.st s with
      | Some v ->  R.union acc (reach ctx v)
      | _ ->
      let _ = printf "stack: %s\n" (st_tostring ctx.st) in
      let _ = List.map (Var.to_list free) (fun s -> printf "%s," s) in
      raise (Fail ("unbound variable 1: " ^ s)))

let rec eval : context -> Typedtree.expression -> value * (value H.t) * int =
  fun ctx exp -> match exp.exp_desc with
  | Texp_ident (path,_,_) ->
    (match V.find ctx.st (Path.name path) with
    | Some v -> v, ctx.hp, ctx.m
    | _ -> raise (Eval "unbound variable 2"))

  | Texp_constant c ->
    (match c with
     | Asttypes.Const_int i ->
      if ctx.m > 0 then
        let l = new_loc () in
        let v = Nat (i, l) in
        v, H.add ctx.hp l v, ctx.m - 1
      else raise (Eval "freelist insufficient")
     | _ -> raise (Eval "unsupported constant"))

  | Texp_let (_, [], e) -> eval ctx e
  | Texp_let (rflag, ({pat_desc = Tpat_var (ident,_)} as p,e1)::xs, e2) ->
    let e' = {exp with exp_desc = Texp_let (rflag, xs, e2)} in
    let r' = R.union ctx.r (locs ctx (mk_exp (exp.exp_env) (Texp_function ("", [p,e'], Total)) (Ctype.newty (Types.Tarrow ("",p.pat_type,e'.exp_type,Types.Cok))))) in
    let v1, hp1, m1 = eval ({ctx with r = r'}) e1 in
    let ctx' = {ctx with st = V.add ctx.st (Path.name (Path.Pident ident)) v1; hp = hp1} in
    let r'' = R.union ctx.r (locs ctx' e') in
    let g = H.filter ctx'.hp ~f:(fun ~key:l ~data:_ -> not (R.mem (hold ctx' r'') l || F.mem ctx.f l)) |> H.keys in
    let _ = printf "g: %s\n" (Int.to_string (List.length g)) in
      eval ({ctx' with m = m1 + List.length g; f = F.union ctx.f (F.of_list g)}) e'

  | Texp_construct (_, {Types.cstr_name = "[]"}, _, _) ->
  if ctx.m > 0 then
    let l = new_loc () in
    let v = Null l in
    let hp' = H.add ctx.hp l v in
    v,hp',ctx.m-1
  else raise (Eval "freelist insufficient")

  | Texp_construct (_, {Types.cstr_name = "::"}, es,_) ->
  if ctx.m > 0 then
    let [v1;v2] = List.map es (fun e ->
      match e.exp_desc with
      | Texp_ident (path,_,_) ->
        (match V.find ctx.st (Path.name path) with
         | Some v -> v
         | _ -> raise (Fail "malformed stack"))
      | _ -> raise (Eval "constructor not in let-normal form")) in
    let l = new_loc () in
    let v = Pair (v1,v2,l) in
    let hp' = H.add ctx.hp l v in
    v,hp',ctx.m-1
  else raise (Eval "freelist insufficient")

  | Texp_construct _ -> raise (Eval "unsupported constructor")

  | Texp_tuple es ->
  if ctx.m > 0 then
    let [v1;v2] = List.map es (fun e ->
      match e.exp_desc with
      | Texp_ident (path,_,_) ->
        (match V.find ctx.st (Path.name path) with
         | Some v -> v
         | _ -> raise (Fail "malformed stack"))
      | _ -> raise (Eval "constructor not in let-normal form")) in
    let l = new_loc () in
    let v = Pair (v1,v2,l) in
    let hp' = H.add ctx.hp l v in
    v,hp',ctx.m-1
  else raise (Eval "freelist insufficient")

  | Texp_match (e,[(_,e1);({pat_desc = Tpat_construct (_,{Types.cstr_name="::"},ps,_)},e2)],_) ->
    begin
    match e.exp_desc with
    | Texp_ident (path,_,_) ->
      (match V.find ctx.st (Path.name path) with
       | Some v ->
          (match v with
           | Null l -> eval ctx e1
           | Pair(v1,v2,l) ->
            let [x1;x2] = List.map ps (fun p -> match p.pat_desc with Tpat_var (ident,_) -> Path.name (Path.Pident ident) | _ -> raise (Eval "pattern not in let-normal form")) in
            let st' = V.add (V.add ctx.st x1 v1) x2 v2 in
            eval ({ctx with st = st'}) e2
           | _ -> raise (Fail "invalid value"))
       | _ -> raise (Fail "malformed stack"))
    | _ -> raise (Eval "match not in let-normal form")
    end

  (* | Texp_function (l,[p,e],part) ->
  | Texp_apply of expression * (label * expression option * optional) list

  | Texp_try of expression * (pattern * expression) list
  | Texp_tuple of expression list

  | Texp_variant of label * expression option
  | Texp_record of
      (Longident.t loc * label_description * expression) list *
        expression option
  | Texp_field of expression * Longident.t loc * label_description
  | Texp_setfield of
      expression * Longident.t loc * label_description * expression
  | Texp_array of expression list
  | Texp_ifthenelse of expression * expression * expression option
  | Texp_sequence of expression * expression *)

let get_eval : structure -> expression =
  function {str_items = [i]} ->
    match i.str_desc with
    | Tstr_eval e -> e

let bound ctx e n =
  let rec trying i =
    if i > n then raise (Eval "insufficient freelist")
    else
      try
        let _,_,m' = eval {ctx with m = i} e in i,m'
      with Eval "freelist insufficient" -> trying (i+1)
  in
    trying 0

let main () =
  if Array.length Sys.argv <> 3 then raise (Fail "incorrect arity")
  else
  let file = Sys.argv.(1) in
  let freelist = Sys.argv.(2) |> Int.of_string in
  let s = In_channel.read_all file in
  let ast = s |> Lexing.from_string |> Parse.implementation in
  let env =
    Compmisc.init_path false;
    Compmisc.initial_env () in
  let tree,_,_ =
  try Typemod.type_structure env ast Location.none
  with Typetexp.Error (_,_,error) -> Typetexp.report_error env Format.std_formatter error; raise (Fail "") in
  let _ = Printtyped.implementation Format.std_formatter tree in
  let e = get_eval tree in
  let empty = {m=freelist;st=V.empty;hp=H.empty;r=R.empty;f = F.empty} in
  let v,hp',m' = eval empty (get_eval tree) in
  let _ = printf "value: %s\nm: %d\nm': %d\n\n" (val_tostring v) freelist m' in
  let high,remain = bound empty e freelist in
  printf "high water mark: %d\nremain: %d\n\n" high remain
;;
main ()
