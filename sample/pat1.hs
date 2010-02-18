main = let { (p, (q, r)) = (print 1, (print 2, print 3)) } in
       q
