circuit swap =
  signal s1 = 4 in
  signal s2 = 6 in
  signal t = 0 in
  ~t <- ~s1;
  ~s1 <- ~s2;
  ~s2 <- ~t 