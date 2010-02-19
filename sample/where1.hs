main = print (fact 10)
  where fact x = if x == 0 then 1 else x * fact (x - 1)
--  where fact 0 = 1
--        fact x = x * fact (x - 1)
