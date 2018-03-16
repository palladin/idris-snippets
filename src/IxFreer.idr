module IxFreer

Eff : Type -> Type
Eff r = r -> (a : Type) -> (a -> r) -> Type

data IxFreer : {r : Type} -> (f : Eff r) -> Eff r where
  Pure : (x : a) -> IxFreer f (s' x) a s'
  Bind : {f : Eff r} -> f s a s' -> ((x : a) -> IxFreer f (s' x) b s'') -> IxFreer f s b s''


(>>=) : IxFreer f s a s' -> ((x : a) -> IxFreer f (s' x) b s'') -> IxFreer f s b s''
(>>=) (Pure x) f = f x
(>>=) (Bind x f) g = Bind x (\y => f y >>= g)

-- Example from https://www.idris-lang.org/drafts/sms.pdf
data Access = LoggedOut | LoggedIn
data LoginResult = OK | BadPassword

data Store : Access -> (ty : Type) -> (ty -> Access) -> Type where
  Login : Store LoggedOut LoginResult (\res => case res of
                                                  OK => LoggedIn
                                                  BadPassword => LoggedOut)

  Logout : Store LoggedIn () (const LoggedOut)
  ReadSecret : Store LoggedIn String (const LoggedIn)
  Lift : IO ty -> Store st ty (const st)


login : IxFreer Store LoggedOut LoginResult (\res => case res of
                                                      OK => LoggedIn
                                                      BadPassword => LoggedOut)
login = Bind Login Pure

logout : IxFreer Store LoggedIn () (const LoggedOut)
logout = Bind Logout Pure

readSecret : IxFreer Store LoggedIn String (const LoggedIn)
readSecret = Bind ReadSecret Pure

lift : IO ty -> IxFreer Store st ty (const st)
lift io = Bind (Lift io) Pure

getData : IxFreer Store LoggedOut () (const LoggedOut)
getData = do result <- login
             case result of
               OK => do secret <- readSecret
                        lift (putStr ("Secret: " ++ show secret ++ "\n"))
                        logout
               BadPassword => lift (putStr "Failure\n")

run : IxFreer Store s () s' -> IO ()
run (Pure x) = pure x
run (Bind Login g) = run (g OK)
run (Bind Logout g) = run (g ())
run (Bind ReadSecret g) = run (g "secret")
run (Bind (Lift io) g) = io >>= \x => run (g x)

test : IO ()
test = run getData
