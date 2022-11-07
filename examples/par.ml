 circuit c =
  output o;
  signal count = 0 in
  signal sum = 0 in
  ((~count <- ~count + 1) // (~sum <- ~sum + ~count; ?o <- ~sum))

