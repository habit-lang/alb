-- ### Examples using if then else expressions:

cond0 x y = if x then 1 else 2
cond1 x y = if x then if y then 1 else 2 else 3
cond2 x y = if x then 1 else if y then 2 else 3
cond3 x y = if x then
              if y then 1 else 2
            else
              if y then 3 else 4

cond4 x y = if x then 
               1
            else if y then
               2
            else
               3

cond4a x y = if<- x 
             then y
             else z

cond4d x y = if<- x 
             then 1
             else if<- y
                  then 2
                  else 3

-- From discussion: this ought to work, but there's a decent justification for why it doesn't at the
-- moment.  The relevant point here has to do with the block that begins following a then in an
-- if-from construct.  That block begins at the second if<- keyword; then associated then is
-- dedented, causing the block to end.  This results in (basically) else { if <- y } then, which
-- predictably fails to parse.  We could either work around this notion particularly for else if
-- chains, or find some general specification for not starting new blocks similar to the one for not
-- adding semicolons in front of some keywords.

-- cond4b x y = if<- x 
--              then 1
--              else if<- y
--              then 2
--              else 3

cond4c x y = if<- x then
               1
             else if<- y then
               2
             else
               3
             
cond5 x y = do if x then 
                  1
               else if<- y then
                 2
               else
                 3

-- Error cases (misformed conditionals):
-- TODO: we don't recover from errors at all...
-- cand0 x y = if x then 1 
-- cand1 x y = if x then if y then 1 else 2
-- cand2 x y = if x else if y else 3
-- cand3 x y = if x then
--             else
--               if y then 3 else 4
-- cand4 x y = if x else 2 
-- cand5 x y = if x
-- cand6 x y = if then else
-- 
-- id x = x -- A test line that should be accepted without errors;
--          -- checks that we recovered ok from above errors ...

