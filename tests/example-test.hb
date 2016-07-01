requires test

-- To write a test, make your "main" look like this and add the file
-- to "TESTS" in the "Makefile".  runTests expects a list of "M Bool"
-- that return True if the test passes and False if the test fails.

main = do
  x <- runTests (Cons (return True) (Cons (return (True == True)) Nil))
  return x
