circuit twice_plus_one n =
  output o, u;
  ?u <- 5;
  let compose = fun f -> 
                ?o <- 42; 
                fun g -> 
                fun x -> f (g x) in
    let inc x = x + 1
    and twice x = x * 2 in
    compose inc twice n

