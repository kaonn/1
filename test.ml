let f = 0 in
let x = 1 in
let y = x in
let z = 3 in
let w = z in
let v = w in
let q = [] in
let q1 = y::q in
let q2 = x::q1 in
match q2 with
| [] -> 1
| u1::u2 -> u1
