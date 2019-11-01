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
  map f (KC k) = KC (\c => k c >>= (\(x, c) => Pure (f x, c)))

Applicative (Kernel sig c) where
  pure a = KC (\c => Pure (a, c))

  (KC f) <*> (KC k) = KC (\c => do (f', c') <- f c
                                   (x, c'') <- k c'
                                   Pure (f' x, c''))

Monad (Kernel sig c) where
  (KC k) >>= f = KC (\c => do (x, c') <- k c
                              let (KC k') = f x
                              k' c')

getUserEff : User sig a -> Eff sig a
getUserEff (UC eff) = eff

getKernelEff : c -> Kernel sig c a -> Eff sig (a, c)
getKernelEff c (KC k) = k c

getEnv : Kernel sig c c
getEnv = KC (\c => Pure (c, c))

setEnv : c -> Kernel sig c ()
setEnv c' = KC (\c => Pure ((), c'))

kernel : Kernel sig c a -> c -> (a -> c -> User sig b) -> User sig b
kernel (KC k) c f = UC $ do (x, c') <- k c
                            let (UC eff) = f x c'
                            eff

performU : {auto e : Exists sig eff} -> eff a -> User sig a
performU op = UC (send op)

performK : {auto e : Exists sig eff} -> eff a -> Kernel sig c a
performK op = KC (\c => send op >>= (\x => Pure (x,c)))

data Runner : (sig : List (Type -> Type)) -> (sig' : List (Type -> Type)) -> (c : Type) -> Type where
  Empty : Runner [] sig' c
  CoOps : ({b : Type} -> eff b -> Kernel sig' c b) -> Runner sig sig' c -> Runner (eff :: sig) sig' c

mkRunner : ({b : Type} -> eff b -> Kernel sig c b) -> Runner [eff] sig c
mkRunner coops = CoOps coops Empty

runOp : Runner sig sig' c -> Exists sig eff -> eff b -> Kernel sig' c b
runOp Empty Here _ impossible
runOp Empty (There _) _ impossible
runOp (CoOps coop coops) Here eff = coop eff
runOp (CoOps coop coops) (There e) eff = runOp coops e eff

runAux : Runner sig sig' c -> c -> User sig a -> (a -> c -> User sig' b) -> User sig' b
runAux r c (UC (Pure x)) uf = uf x c
runAux r c (UC (Bind {e} eff f)) uf = kernel (runOp r e eff) c (\x, c' => runAux r c' (UC $ f x) uf)

run : Runner sig sig' c -> User sig' c -> User sig a -> (a -> c -> User sig' b) -> User sig' b
run r ui u uf = ui >>= (\c => runAux r c u uf)

-- Example

testKernel : Kernel [State Int] Int Int
testKernel = do c <- performK Get
                performK (Put (c + 1))
                pure c

testRunner : Runner [Reader Int] [State Int] Int
testRunner = mkRunner  (\Ask => testKernel)

testInit : User [State Int] Int
testInit = do c <- performU Get
              pure (c + 1)

testUser : User [Reader Int] Int
testUser = do x <- performU Ask
              pure x

testFinaliser : Int -> Int -> User [State Int] Int
testFinaliser x c = pure x

testRun : User [State Int] Int
testRun = run testRunner testInit testUser testFinaliser

test : (Int, Int)
test = run $ runState 0 $ getUserEff testRun
