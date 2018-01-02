module Unlambda

import Control.Monad.Trans
import src.ContT

-- Based on http://www.madore.org/~david/programs/unlambda/

data Rec : (r : Type) -> (m : Type -> Type) -> Type where
  RecK : (Rec r m -> ContT r m (Rec r m)) -> Rec r m


data Expr : Type where
  S : Expr
  K : Expr
  I : Expr
  R : Expr
  C : Expr
  Dot : Char -> Expr
  Backtick : Expr -> Expr -> Expr

apply : ContT r m (Rec r m) -> ContT r m (Rec r m) -> ContT r m (Rec r m)
apply first second = do (RecK k) <- first
                        b <- second
                        k b

eval : Monad m => Expr -> (Char -> m ()) -> ContT r m (Rec r m)
eval S put = pure $ RecK (\rec =>
             pure $ RecK (\rec' =>
             pure $ RecK (\rec'' => apply (apply (pure rec) (pure rec'')) (apply (pure rec') (pure rec'')))))
eval K put = pure $ RecK (\rec => pure $ RecK (\_ => pure rec))
eval I put = pure $ RecK (\rec => pure rec)
eval R put = pure $ RecK (\rec => do lift $ put '\n'; pure rec)
eval C put = pure $ RecK (\(RecK k) => callCC (\k' => k $ RecK k'))
eval (Dot char) put = pure $ RecK (\rec => do lift $ put char; pure rec)
eval (Backtick expr expr') put = apply (eval expr put) (eval expr' put)


parse :  List Char -> Maybe (Expr, List Char)
parse ('s' :: xs) = Just (S, xs)
parse ('k' :: xs) = Just (K, xs)
parse ('i' :: xs) = Just (I, xs)
parse ('r' :: xs) = Just (R, xs)
parse ('c' :: xs) = Just (C, xs)
parse ('.' :: c :: xs) = Just (Dot c, xs)
parse ('`' :: xs) = do (expr, xs') <- parse xs
                       (expr', xs'') <- parse xs'
                       Just (Backtick expr expr', xs'')
parse (x :: xs) = Nothing
parse [] = Nothing

callCCTest : String
callCCTest = "``cir"

helloWorldTest : String
helloWorldTest = "```si`k``s.H``s.e``s.l``s.l``s.o``s. ``s.w``s.o``s.r``s.l``s.d``s.!``sri``si``si``si``si``si``si``si``si`ki"

example : IO ()
example = case parse (unpack helloWorldTest) of
            Just (expr, _) => run (\_ => pure ()) $ eval expr putChar
            Nothing => putStrLn "Parse error"
