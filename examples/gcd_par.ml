circuit test i1 i2 i3 i4 =
  let rec gcd a b =
    if a > b then gcd (a-b) b else
    if a < b then gcd a (b-a) else a 
  in 
  let u = gcd i1 i2 
  and v = gcd i3 i4 
  in u + v;;