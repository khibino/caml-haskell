foo x y
    | True  = x + y
    | False = x - y

bar x y
    | True  = x <= y
    | False = y <= x

main = bar (foo 1 2) 3
