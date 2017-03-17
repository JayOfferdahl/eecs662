eval :: Env -> BBAE -> (Either String BBAE)

-- evaluates l and binds the result to l'
eval env (Plus l r) = do l' <- eval env l
                         r' <- eval env r

-- When evaluating in this case, you could get a left or a right
-- If you get a (Right ) --> bind result to l', if you get a left, fall through.

-- Again, if a (Left e) is found when evaluating r, fall all the way out
-- if you get a (Right x), you move onto the next piece (return PlusNum r' l'))
-- Return within the either monad corresponds to (Right ...)