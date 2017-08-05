let rec append l1 l2= 
  match l1 with
  | [] -> l2
  | x::xs -> x :: append xs l2
in

let x = [1] in
let y = [6] in
let r1 = append x y in
r1
