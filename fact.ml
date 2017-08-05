(*
let rec fact n = 
  let z = 0 in 
  let e = n = z in
  if e
  then 
    let o = 1 in 1
  else 
    let rarg = n - 1 in 
    let r = fact rarg in 
    n * r
in 
let arg = 20 in 
fact arg
*)

let rec fact n = if n = 0 then 1 else n * fact (n-1) in 
fact 5
