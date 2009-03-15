(define (1- x)
  (- x 1))

(define (less-or-eq x y)
  (print "DEBUG: called '<=' with " x " " y)
  (<= x y))

(define (tarai x y z)
  (cond ((less-or-eq x y) y)
       	(#t (tarai
             (tarai (1- x) y z)
             (tarai (1- y) z x)
             (tarai (1- z) x y)))))
