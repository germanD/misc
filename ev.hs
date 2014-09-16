{-# OPTIONS -XMultiParamTypeClasses -XFunctionalDependencies #-}
{-# OPTIONS -XFlexibleInstances  -XFlexibleContexts  #-}

module IdiocraticEval where

import Prelude
import Control.Monad.State

-- An Idiocratic Arithmetic Evaluator: first attempt

data Ev s a = EV { ev :: Either s (s -> s) -> (a , Either s (s -> s)) }

runEv  :: s -> Ev s a -> a
runEv s0 m = fst $ ev m (Left s0)

instance Monad (Ev s) where
    return x = EV $ \ es -> (x,es)
    (>>=) m k = EV $ \ es -> let (b , s2) = ev m es 
                             in ev (k b) s2

instance MonadState (Either s (s->s)) (Ev s) where
    put s1 = EV $ \ _ -> ((),s1)
    get = EV $ \ es -> (es,es)


push           :: (Either s (s -> s -> s)) -> Ev s ()
push (Left s1)  =  get >>= \ x -> case x of
                                    (Left s) -> put $ Left $ s1
                                    (Right f) -> put $ Left $ f s1 
push (Right op) = get >>= \ x  -> case x of
                                   (Left s) -> put $ Right $ op s
                                   (Right f) -> put $ Right f

-- Argh... This'll only work for well-formed expressions. 
-- In a simple calculator pressing +, x will forget +, not x.

mauro1 :: [ Either Int ( Int -> Int -> Int)] 
mauro1 = [Left 1 , Right (+), Left 1, Right (+), Left 1, Right (*) , Left 0]


-- I'm beyond being nice. After all, this is an idiocratic evaluator

solve1 ss =  case  (runEv 0 $ foldr (\ b ms ->  push b >> ms) get ss) of
               (Left n) -> putStrLn $ "I'm the king of Facebook math: " ++ (show n)
               (Right _) -> putStrLn "We suckz"