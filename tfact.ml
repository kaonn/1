let rec fact t = 
  let n = fst t in 
  let acc = snd t in 
  let z = 0 in 
  let e = n = z in 
  if e then acc
  else 
    let n1 = n - 1 in 
    let acc' = acc * n in 
    let arg = (n1, acc') in 
    fact arg 
in 
  let n = 20 in 
  let acc = 1 in 
  let arg = (n,acc) in 
  fact arg
