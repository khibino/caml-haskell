--     *  TARAI funciton: Original definition of TAK Function

--       (defun tarai (x y z)
--         (cond ((> x y)
--       	 (tarai
--       	  (tarai (1- x) y z)
--       	  (tarai (1- y) z x)
--       	  (tarai (1- z) x y) ))
--       	(t y) ))


--     * TAK function : John Macarthy's variation of TARAI function

--       (defun tak (x y z)
--         (cond ((not (< y x)) z)
--       	(t
--       	  (tak
--       	    (tak (1- x) y z)
--       	    (tak (1- y) z x)
--       	    (tak (1- z) x y)))))

tarai x y z
    | x <= y = y
    | True   = tarai
               (tarai (x - 1) y z)
               (tarai (y - 1) z x)
               (tarai (z - 1) x y)

--main = print (tarai 2 1 1)
main = print (tarai 1 1 (1 + 0))
--main = print (tarai 5 1 1)
--main = print (tarai 0 0 0)
--main = print (tarai 10 3 1)
