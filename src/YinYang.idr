module YinYang

import Control.Monad.Trans
import snippets.ContT

data Rec : (r : Type) -> (m : Type -> Type) -> Type where
  RecK : (Rec r m -> ContT r m (Rec r m)) -> Rec r m

yin : ContT r IO (Rec r IO)
yin = do k <- callCC (\k => pure (RecK k))
         lift (putStrLn "")
         pure k

yang : ContT r IO (Rec r IO)
yang = do k <- callCC (\k => pure (RecK k))
          lift (putStr "*")
          pure k

yinyang : ContT r IO (Rec r IO)
yinyang = do (RecK k) <- yin
             k' <- yang
             k k'

test : IO ()
test = run (\_ => pure ()) yinyang
