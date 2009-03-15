f x y
  | x <= y = y
  | True   = x

main = print (f 2 1)
