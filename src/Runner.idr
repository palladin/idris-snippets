module Runner

-- Based on https://arxiv.org/pdf/1910.11629.pdf
--          https://github.com/danelahman/haskell-coop

import Src.Eff

data User : (sig : List (Type -> Type)) -> (a : Type) -> Type where
  UC : Eff sig a -> User sig a

Functor (User sig) where
  map f (UC eff) = UC $ eff >>= (\x => Pure $ f x)

Applicative (User sig) where
  pure a = UC $ Pure a

  (UC effF) <*> (UC eff) = UC $ eff >>= (\x => effF >>= (\f => Pure $ f x))

Monad (User sig) where
  (UC eff) >>= f = UC $ eff >>= (\x => let (UC eff') = f x in eff')


data Kernel : (sig : List (Type -> Type)) -> (c : Type) -> (a : Type) -> Type where
  KC : (c -> Eff sig (a, c)) -> Kernel sig c a

Functor (Kernel sig c) where
  map f (KC g) = KC (\c => g c >>= (\(x, c) => Pure (f x, c)))

Applicative (Kernel sig c) where
  pure a = KC (\c => Pure (a, c))

  (KC f) <*> (KC k) = KC (\c => do (f', c') <- f c
                                   (x, c'') <- k c'
                                   Pure (f' x, c''))

Monad (Kernel sig c) where
  (KC k) >>= f = KC (\c => do (x, c') <- k c
                              let (KC k') = f x
                              k' c')
