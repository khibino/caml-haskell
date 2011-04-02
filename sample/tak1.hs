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

taky x y z 
    | x <= y = y
    | True   = taky
               (taky (x - 1) y z)
               (taky (y - 1) z x)
               (taky (z - 1) x y)

main = print (taky 100 50 0)
--main = print (taky 14 7 0)
--main = print (taky 0 0 0)
--main = print (taky 10 3 1)
