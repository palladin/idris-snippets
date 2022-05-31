module EffContSimp

Cont : Type -> Type -> Type
Cont r a = (a -> r) -> r

pure : a -> Cont r a
pure x k = k x

(>>=) : Cont r a -> (a -> Cont r b) -> Cont r b
(>>=) m f k = m (\x => f x k)

Handler : Type -> (Type -> Type) -> Type -> Type
Handler r p a = p a -> (a -> r) -> r

op : p a -> Cont (Handler r p a -> r) a
op v k h = h v (\x => k x h)

handle : Cont (Handler r p a -> r) a -> Handler r p a -> (a -> r) -> r
handle m h k = m (\x, h => k x) h


example : Cont (Handler r Maybe Int -> r) Int
example = do x <- op $ Just 42
             --y <- op $ Just "42"
             pure $ x + 1

test : Maybe Int
test = handle example (\x, k => case x of
                                  Just x => k x
                                  Nothing => Nothing) Just
