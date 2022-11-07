circuit gcd_fsm =
  input n, m;
  output result;
  signal a = ?n in
  signal b = ?m in
  automaton
  | idle -> ?result <- ~a; continue idle
  | gcd  -> if ~a > ~b then (~a <- ~a - ~b; continue gcd) else 
            if ~a < ~b then (~b <- ~b - ~a; continue gcd) else
            (?result <- ~a; continue idle)
  in continue idle ;;