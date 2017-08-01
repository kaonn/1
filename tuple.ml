let fst t = match t with (a,b) -> a in 
let snd t = match t with (a,b) -> b in
let x = (1,2,3,4,5) in
let z = x in 
let y = (1,(2,(3,(4,5)))) in 
match z with 
| (a,b,c,d,e) -> e < 1
