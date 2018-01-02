module ZipperTraversable

-- Based on http://okmij.org/ftp/continuations/zipper.html#traversable

import Control.Monad.Identity
import snippets.ContT

data Zipper : (t : Type -> Type) -> (a : Type) -> Type where
  ZDone : t a -> Zipper t a
  Z : a -> (Maybe a -> Zipper t a) -> Zipper t a


makeZipper : Traversable t => t a -> Zipper t a
makeZipper tr = runIdentity . reset $ traverse f tr >>= pure . ZDone
  where
    f : a -> Cont (Zipper t a) a
    f a = shift (\k => pure $ Z a (runIdentity . k . maybe a id))

update : Zipper List Int -> List Int
update (ZDone x) = x
update (Z x f) = update $ f (Just (x + 1))

test : List Int
test = update $ makeZipper [1..10]
