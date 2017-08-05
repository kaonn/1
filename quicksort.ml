let fst t = match t with (a,b) -> a in 
let snd t = match t with (a,b) -> b in

let rec append l1 l2 =
  match l1 with
    | [] -> l2
    | x::xs -> x::(append xs l2) 
in 


let rec partition f l =
  match l with
    | [] -> ([],[])
    | x::xs ->
      let t = partition f xs in
      let cs = fst t in 
      let bs = snd t in
      if f x then
	(cs,x::bs)
      else
	(x::cs,bs) 
in

let rec quicksort gt l = 
  match l with
  | [] -> []
  | x::xs ->
      let t = partition (gt x) xs in
      let ys = fst t in 
      let zs = snd t in
      append (quicksort gt ys) (x :: (quicksort gt zs))

in

quicksort (fun a b -> a <= b) ([3;2;1])
