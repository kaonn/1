let stack : context -> expression -> value =
  fun ctx e ->
  match e.exp_desc with
  | Texp_ident (path,_,_) ->
    (match V.find ctx.st (Path.name path) with
     | Some v -> v
     | _ -> raise (Fail "malformed stack"))
  | _ -> raise (Eval "expression not in let-normal form")

(*let rec eval : context -> Typedtree.expression -> value * (value H.t) * int =
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
    let [v1;v2] = List.map es (stack ctx) in
    let l = new_loc () in
    let v = Pair (v1,v2,l) in
    let hp' = H.add ctx.hp l v in
    v,hp',ctx.m-1
  else raise (Eval "freelist insufficient")

  | Texp_construct _ -> raise (Eval "unsupported constructor")

  | Texp_tuple es ->
  if ctx.m > 0 then
    let [v1;v2] = List.map es (stack ctx) in
    let l = new_loc () in
    let v = Pair (v1,v2,l) in
    let hp' = H.add ctx.hp l v in
    v,hp',ctx.m-1
  else raise (Eval "freelist insufficient")

  | Texp_match (e,[(_,e1);({pat_desc = Tpat_construct (_,{Types.cstr_name="::"},ps,_)},e2)],_) ->
    begin
    match stack ctx e with
    | Null l -> eval ctx e1
    | Pair(v1,v2,l) ->
      let [x1;x2] = List.map ps (fun p -> match p.pat_desc with Tpat_var (ident,_) -> Path.name (Path.Pident ident) | _ -> raise (Eval "pattern not in let-normal form")) in
      let st' = V.add (V.add ctx.st x1 v1) x2 v2 in
      eval ({ctx with st = st'}) e2
    | _ -> raise (Fail "invalid value")
    end

  | Texp_function (_,[{pat_desc = Tpat_var(ident,_)},e],_) ->
  if ctx.m > 0 then
    let l = new_loc () in
    let v = Cl (ctx.st, Path.name (Path.Pident ident), e, l) in
    let hp' = H.add ctx.hp l v in
    v,hp',ctx.m-1
  else raise (Eval "freelist insufficient")

  | Texp_apply (f, [_,eo,_]) ->
    match eo with
    | Some arg ->
      let v = stack ctx arg in
      let (Cl(cl,x,e',l)) = stack ctx f in
      let cl' = V.add cl x v in
      let ctx' = {ctx with st = cl'} in
      eval ctx' e'
      *)

