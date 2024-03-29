module EffContSimp

Cont : Type -> Type -> Type
Cont r a = (a -> r) -> r

pure : a -> Cont r a
pure x k = k x

(>>=) : Cont r a -> (a -> Cont r b) -> Cont r b
(>>=) m f k = m (\x => f x k)

Handler : Type -> (Type -> Type) -> Type
Handler r p = {a : Type} -> p a -> (a -> r) -> r

op : p a -> Cont (Handler r p -> r) a
op v k h = h v (\x => k x h)

handle : Cont (Handler r p -> r) a -> Handler r p -> (a -> r) -> r
handle m h k = m (\x, h => k x) h


example : Cont (Handler r Maybe -> r) String
example = do x <- op $ Just 42
             y <- op $ Just "42"
             pure $ cast x ++ " " ++ y

test : Maybe String
test = handle example (\x, k => case x of
                                  Just x => k x
                                  Nothing => Nothing) Just
