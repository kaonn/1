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
module P = Map.Make(String)

type loc = int


type value = Nat of int * loc | T of loc | F of loc | Null of loc | Loc of loc * loc | Pair of value * value * loc | Cl of (value V.t) * string option * string * expression * loc 
           | Cont of (context -> value -> result)
and result = value * (value H.t) * F.t
and context = {st : value V.t; hp : value H.t; r : R.t; f : F.t; b : string option}

let init : int -> F.t = fun n -> 
  List.init n (fun i -> i) |> F.of_list

let new_loc : F.t -> loc * F.t =
  fun freelist ->
    let min = F.min_elt freelist in 
    match min with 
    | Some m -> let f' = F.remove freelist m in m, f' 
    | _ -> raise (Fail "cannot alloc from empty freelist")

let get_loc : value -> loc = 
  function Nat (_,l) | T l | F l | Null l | Loc (_,l) | Pair (_,_,l) | Cl (_,_,_,_,l) -> l
  
let pervasives = P.of_alist_exn [
  ("Pervasives.<",
    Cont(
    fun ctx (Nat (a,_)) -> 
      Cont(
        fun ctx (Nat(b,_)) -> 
          let l,f' = new_loc ctx.f in 
          let v = if a < b then T l else F l in 
          let hp' = H.add ctx.hp l v in 
          v,hp',f'
      )
      , ctx.hp
      , ctx.f
    )
    
  )
  ;
  ("Pervasives.<=",
    Cont(
    fun ctx (Nat (a,_)) -> 
      Cont(
        fun ctx (Nat(b,_)) -> 
          let l,f' = new_loc ctx.f in 
          let v = if a <= b then T l else F l in 
          let hp' = H.add ctx.hp l v in 
          v,hp',f'
      )
      , ctx.hp
      , ctx.f
    )
    
  )
  ;
  ("Pervasives.=",
    Cont(
    fun ctx (Nat (a,_)) -> 
      Cont(
        fun ctx (Nat(b,_)) -> 
          let l,f' = new_loc ctx.f in 
          let v = if a = b then T l else F l in 
          let hp' = H.add ctx.hp l v in 
          v,hp',f'
      )
      , ctx.hp
      , ctx.f
    )
    
  )

  ;
  ("Pervasives.-",
    Cont(
    fun ctx (Nat (a,_)) -> 
      Cont(
        fun ctx (Nat(b,_)) -> 
          let l,f' = new_loc ctx.f in 
          let v = Nat (a - b, l) in
          let hp' = H.add ctx.hp l v in 
          v,hp',f'
      )
      , ctx.hp
      , ctx.f
    )
    
  )
  ;
  ("Pervasives.*",
    Cont(
    fun ctx (Nat (a,_)) -> 
      Cont(
        fun ctx (Nat(b,_)) -> 
          let l,f' = new_loc ctx.f in 
          let v = Nat (a * b, l) in
          let hp' = H.add ctx.hp l v in 
          v,hp',f'
      )
      , ctx.hp
      , ctx.f
    )
    
  )
  ;
  ("Pervasives.fst",
    Cont(fun ctx (Pair (v1,v2,_)) -> v1 , ctx.hp , ctx.f)
  )
  ;
  ("Pervasives.snd",
    Cont(fun ctx (Pair (v1,v2,_)) -> v2 , ctx.hp , ctx.f)
  )

]

let rec val_tostring : value -> string =
  function (Nat (i, l)) -> (Int.to_string i) ^ "@" ^ (Int.to_string l)
  | T l -> "T@" ^ Int.to_string l
  | F l -> "F@" ^ Int.to_string l
  | Null l -> "Null@"  ^Int.to_string l
  | Loc (l1,l2)  -> "L:" ^ (Int.to_string l1) ^ "@" ^ (Int.to_string l2)
  | Pair (v1,v2,l) -> "<" ^ (val_tostring v1) ^ ", " ^ (val_tostring v2) ^ ">@" ^ Int.to_string l
  | Cl (cl,o,x,e,l) -> "[ " ^ "<<stack>>" ^ ", " ^ (match o with Some n -> "fix: " ^ n | _ -> "fix: _") ^ ", " ^ x ^ ".<body>]@" ^ Int.to_string l

and st_tostring : value V.t -> string =
  fun st ->
  "V : " ^ List.fold_right (List.map (V.to_alist st) (fun (x,v) -> x ^ " -> " ^ val_tostring v ^ ", ")) ~init:"" ~f:(fun a b -> a^b)

let free_to_string free = "\n{" ^ F.fold free ~init:"" ~f:(fun acc e -> acc ^ Int.to_string e ^ ", ") ^ "}\n"


let bound_set = ref Var.empty
let free_set = ref Var.empty

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

let bound_names p = List.map (pat_bound_idents p) (fun (ident,_) -> Path.name (Path.Pident ident)) |> Var.of_list

let fv bound exp =

  let rec traverse bound_set exp =
    match exp.exp_desc with
    | Texp_ident (path,_,_) ->
      if Var.mem bound_set (Path.name path) then Var.empty else Var.singleton (Path.name path)
    | Texp_constant _ -> Var.empty
    | Texp_let (_,[],e) -> traverse bound_set e
    | Texp_let (rflag,(p,e)::xs,e1) ->
      let rec_bind = match rflag with Asttypes.Recursive -> bound_names p | _ -> Var.empty in 
      let f1 = traverse (Var.union bound_set rec_bind) e in
      let e' = {exp with exp_desc = Texp_let (rflag,xs,e1)} in
      let f2 = traverse (Var.union bound_set (bound_names p)) e' in
      Var.union f1 f2

    | Texp_function (_,pes,_) -> List.map pes (fun (p,e) -> traverse (Var.union bound_set (bound_names p)) e) |> Var.union_list

    | Texp_apply (e,es) ->
      let f1 = traverse bound_set e in
      let f2 = List.map es (fun (_,eo,_) -> match eo with Some e' -> traverse bound_set e' | _ -> Var.empty) |> Var.union_list in
      Var.union f1 f2

    | Texp_match (e,pes,_) ->
      let f1 = traverse bound_set e in
      let f2 = List.map pes (fun (p,e) -> traverse (Var.union bound_set (bound_names p)) e)  |> Var.union_list in
      Var.union f1 f2

    | Texp_tuple es -> List.map es (traverse bound_set) |> Var.union_list

    | Texp_construct (_,_,es,_) -> List.map es (traverse bound_set) |> Var.union_list

    | Texp_ifthenelse (e,et,Some ef) -> 
        [
          traverse bound_set e;
          traverse bound_set et;
          traverse bound_set ef
        ] |> Var.union_list 

    | Texp_ifthenelse (e,et,_) -> raise (Eval "else branch not optional")

  in
  traverse bound exp

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
  | Cl (cl,o,x,e,l) ->
    let bound = match o with Some n -> Var.of_list [n;x] | _ -> Var.singleton x in
    let free = fv bound e in
    let f1 = List.map (Var.to_list free) (fun var -> (try V.find_exn cl var with _ -> 
     try P.find_exn pervasives var with _ -> raise (Fail var)) |> reach ctx) |> R.union_list in
    R.add f1 l
  | Cont cont -> R.empty

let rec hold : context -> R.t -> R.t =
  fun ctx r ->
    R.fold_right r ~init:R.empty ~f:(fun l acc ->
      match H.find ctx.hp l with
      | Some v -> R.union acc (R.add (reach ctx v) l)
      | _ -> raise (Fail "malformed heap")
    )

let locs : context -> Var.t -> expression-> R.t =
  fun ctx bound e ->
    let free = fv bound e in
    Var.fold_right free ~init:R.empty ~f:(fun s acc ->
      match V.find ctx.st s with
      | Some v ->  R.union acc (reach ctx v)
      | _ -> 
          (match P.find pervasives s with 
           | Some p -> R.union acc (reach ctx p)
           | _ ->
      let _ = printf "stack: %s\n" (st_tostring ctx.st) in
      let _ = List.map (Var.to_list free) (fun s -> printf "%s," s) in
      raise (Fail ("unbound variable 1: " ^ s))))

let rec unravel : int -> value -> value list = 
  fun i v -> 
  if i = 0 then [v] 
  else
  (match v with 
  | Pair (v1,v2,l) -> unravel (i - 1) v1 @ [v2]
  | _ -> raise (Fail "tuple unraveling failed@fct") )

let collect : context -> R.t -> R.t = 
  fun ctx r -> 
  H.filter ctx.hp ~f:(fun ~key:l ~data:_ -> not (R.mem (hold ctx r) l || F.mem ctx.f l)) |> H.keys |> R.of_list
    
let rec eval' : context -> Typedtree.expression -> result = 
fun ctx exp -> match exp.exp_desc with
| Texp_ident (path,_,_) ->
  (match V.find ctx.st (Path.name path) with
  | Some v -> v, ctx.hp, ctx.f
  | _ -> 
      (match P.find pervasives (Path.name path) with 
      | Some p -> p, ctx.hp, ctx.f
      | _ -> raise (Eval "unbound variable 2")))

| Texp_constant c ->
  (match c with
   | Asttypes.Const_int i ->
      let l,f' = new_loc ctx.f in
      let v = Nat (i, l) in
      v, H.add ctx.hp l v, f'
   | _ -> raise (Eval "unsupported constant"))

| Texp_let (_, [], e) -> eval' ctx e
| Texp_let (rflag, ({pat_desc = Tpat_var (ident,_)} as p,e1)::xs, e2) ->
  let e' = {exp with exp_desc = Texp_let (rflag, xs, e2)} in
  let r' = try R.union ctx.r (locs ctx (Var.singleton (Path.name (Path.Pident ident))) e') with _ -> raise (Fail (Path.name (Path.Pident ident))) in 
  let rec_bind = match rflag with Asttypes.Recursive -> Some (Path.name (Path.Pident ident)) | _ -> None in
  let v1, hp1, f1 = eval' ({ctx with r = r'; b = rec_bind}) e1 in
  let ctx' = {ctx with st = V.add ctx.st (Path.name (Path.Pident ident)) v1; hp = hp1; f = f1} in
  let r'' = R.union ctx.r (locs ctx' Var.empty e') in
  let g = collect ctx' r'' in 
  (* let g' = H.filter ctx'.hp ~f:(fun ~key:l ~data:_ -> not (R.mem (hold ctx' r'') l || F.mem ctx'.f l)) |> H.to_alist in
  let _ = 
    printf "garbage at loc (for e1): ";
    Location.print Format.std_formatter e1.exp_loc;
    List.iter g' (fun (l,v) -> printf "\n,%s --> %s" (Int.to_string l) (val_tostring v)); printf "\n" in *)
  eval' ({ctx' with f = F.union ctx'.f g}) e'

| Texp_construct (_, {Types.cstr_name = "[]"}, _, _) ->
  let l,f' = new_loc ctx.f in
  let v = Null l in
  let hp' = H.add ctx.hp l v in
  v,hp',f'

| Texp_construct (_, {Types.cstr_name = "::"}, [e1;e2],_) ->
  let free = locs ctx Var.empty e2 in 
  let ctx1 = {ctx with r = R.union ctx.r free} in 
  let v1,hp1,f1 = eval' ctx1 e1 in
  let ctx2 = {ctx with hp = hp1; f = f1} in 
  let r = R.union ctx.r free in 
  let g = collect ctx2 r in 
  let ctx3 = {ctx2 with f = F.union ctx2.f g} in 
  let v2,hp2,f2 = eval' ctx3 e2 in 
  let l,f' = new_loc f2 in
  let v = Pair (v1,v2,l) in
  let hp' = H.add hp2 l v in
  v,hp',f'

| Texp_construct _ -> raise (Eval "unsupported constructor")

| Texp_tuple (e::es) -> 
  let free = List.map es (locs ctx Var.empty) |> R.union_list in 
  let v1,h1,f1 = eval' {ctx with r = R.union ctx.r free} e in
  List.foldi es ~init:(v1,h1,f1) ~f:(fun i (v,h,f) e -> 
    let after = List.drop es (i+1) in 
    let free = List.map after (locs ctx Var.empty) |> R.union_list in
    let hold = R.add free (get_loc v)  in
    let ctx' = {ctx with hp = h; r = R.union ctx.r hold; f = f} in 
    let g = collect ctx' (R.union ctx'.r (locs ctx' Var.empty e)) in 
    let ctx2 = {ctx' with f = F.union ctx'.f g} in 
    let vc,hc,fc = eval' ctx2 e in 
      let l,f' = new_loc fc in 
      let v' = Pair (v,vc,l) in 
      let hp' = H.add hc l v' in
      v',hp', f')

| Texp_match (e,[{pat_desc = Tpat_tuple ps} as p,e'],_) ->
  let free = locs ctx (bound_names p) e' in 
  let v,hp',f' = eval' {ctx with r = R.union ctx.r free} e in 
  let bound_vars = List.map ps (fun p -> match p.pat_desc with Tpat_var (ident,_) -> Path.name (Path.Pident ident) | _ -> raise (Eval "pattern not in let-normal form")) in
  let vals = unravel (List.length bound_vars - 1) v in 
  let st' = try List.fold2_exn bound_vars vals ~init:ctx.st ~f:(fun acc a b -> V.add acc a b) with Invalid_argument _ -> raise (Fail "tuple unraveling failed") in 
  let ctx' = {ctx with  st = st'; hp = hp';f = f'} in 
  let r = R.union ctx'.r (locs ctx' Var.empty e') in 
  let g = collect ctx' r in 
  let ctx2 = {ctx' with f = F.union ctx'.f g} in 
  eval' ctx2 e'


| Texp_match (e,[({pat_desc = Tpat_construct (_,{Types.cstr_name="[]"},[],_)},e1);({pat_desc = Tpat_construct (_,{Types.cstr_name=name},ps,_)} as p,e2)],_) ->
  begin 
    match name with 
    | "::" -> 
      let free = R.union (locs ctx Var.empty e1) (locs ctx (bound_names p) e2) in 
      let v,hp',f' = eval' {ctx with r = R.union ctx.r free} e in 
      begin
      match v with
      | Null l -> 
      let ctx' = {ctx with f = f'; hp = hp'} in 
      let r = R.union ctx'.r (locs ctx' Var.empty e1) in 
      let g = collect ctx' r in
      let ctx2 = {ctx' with f = F.union ctx'.f g} in
      eval' ctx2 e1
      | Pair(v1,v2,l) ->
        let [x1;x2] = List.map ps (fun p -> match p.pat_desc with Tpat_var (ident,_) -> Path.name (Path.Pident ident) | _ -> raise (Eval "pattern not in let-normal form")) in
        let st' = V.add (V.add ctx.st x1 v1) x2 v2 in
        let ctx' = {ctx with st = st'; f = f'; hp = hp'} in 
        let r = R.union ctx'.r (locs ctx' Var.empty e2) in  
        let g = collect ctx' r in
        let ctx2 = {ctx' with f = F.union ctx'.f g} in
        eval' ctx2 e2
      | _ -> raise (Fail "invalid value: nil or cons expected")
      end
  end
  

| Texp_function (_,[{pat_desc = Tpat_var(ident,_)},e],_) ->
  let l,f' = new_loc ctx.f in
  let v = Cl (ctx.st, ctx.b, Path.name (Path.Pident ident), e, l) in
  let hp' = H.add ctx.hp l v in
  v,hp',f'

| Texp_apply (e1, es) ->
  let args  = List.map es (fun (_,eo,_) -> match eo with Some e -> e | _ -> raise (Eval "labeled arguments not supported")) in 
  let free = List.map args (locs ctx Var.empty) |> R.union_list in 
  let v1,h1,f1 = eval' {ctx with r = R.union ctx.r free} e1 in
  List.foldi args ~init:(v1,h1,f1) ~f:(fun i (fct,h,f) earg -> 
    let after = List.drop args (i + 1) in
    let free = List.map after (locs ctx Var.empty) |> R.union_list in
    match fct with 
    | Cl (cl,name,x,e,l) -> 
    let hold = R.add free l in 
    let ctx' = {ctx with f = f; hp = h; r = R.union ctx.r hold} in 
    let r = R.union ctx'.r (locs ctx' Var.empty earg) in 
    let g = collect ctx' r in
    let ctx2 = {ctx' with f = F.union ctx'.f g} in 
    let arg,hp',f' = eval' ctx2 earg in 
    let st' = V.add cl x arg in
    let st'' = match name with Some fname -> V.add st' fname (Cl(ctx.st,name,x,e,l)) | _ -> st' in 
    let ctx' = {ctx with f = f'; st = st''; hp = hp'; r = R.union ctx.r free} in 
    let r1 = 
    eval' ctx' e

    | Cont cont -> 
    let arg,hp',f' = eval' {ctx with f = f; hp = h; r = R.union ctx.r free} earg in 
    cont {ctx with f = f'; hp = hp'} arg

    | _ -> raise (Fail "cannot apply non-function type"))


| Texp_ifthenelse (e,et,Some ef) -> 
    let free = R.union (locs ctx Var.empty et) (locs ctx Var.empty ef) in 
    let v,hp',f' = eval' {ctx with r = R.union ctx.r free} e in 
    let ctx' = {ctx with f = f'; hp = hp'} in 
    begin
      match v with
    | T _ -> eval' ctx' et
    | F _ -> eval' ctx' ef
    | _ -> raise (Fail "invalid value: bool expected")
    end

| Texp_ifthenelse (e,et,_) -> raise (Eval "else branch not optional")

| _ ->
    raise (Eval "unsupported expression")


    
(*   | Texp_sequence of expression * expression  *)

let get_eval : structure -> expression =
  function {str_items = [i]} ->
    match i.str_desc with
    | Tstr_eval e -> e

let bound ctx e n =
  let rec trying i =
    if i > n then raise (Eval "insufficient freelist")
    else
      try
        let free = init i in
        let _,_,f' = eval' {ctx with f = free} e in i,f'
      with Eval "freelist insufficient" -> trying (i+1)
  in  
    trying 0

let main () =
  if Array.length Sys.argv <> 3 then raise (Fail "incorrect arity")
  else
  let file = Sys.argv.(1) in
  let free = Sys.argv.(2) |> Int.of_string in
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
  let freelist = init free in
  let empty = {f=freelist;st=V.empty;hp=H.empty;r=R.empty; b = None} in
  let v,hp',f' = eval' empty (get_eval tree) in
  let _ = printf "value: %s\nf: %s\nf': %s\n\n" (val_tostring v) (free_to_string freelist) (free_to_string f') in ()
(*
  let high,remain = bound empty e freelist in
  printf "high water mark: %d\nremain: %d\n\n" high remain
*)
;;
main ()
