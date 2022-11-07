circuit absolute_value =
  input i;
  output o;
  ?o <- (if ?i < 0 then 0 - ?i else ?i)

