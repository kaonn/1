let rec append l1 l2= 
  match l1 with
  | [] -> l2
  | x::xs ->[]
in

let x = [] in
let y = [] in
let r1 = append x y in
r1
