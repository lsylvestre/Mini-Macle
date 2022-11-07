circuit f =
  input i1, i2; 
  output o1, o2; 
  
  let counter o i init step =
    signal s = 0 in
    automaton 
    | q -> if ?i then (~s <- ~s+step; ?o <- ~s); continue q
    in ~s <- init; continue q 
  in
  
  (counter o1 i1 0 1) // (counter o2 i2 0 10) ;;
