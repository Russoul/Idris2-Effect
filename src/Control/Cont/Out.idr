module Control.Cont.Out

import Control.HigherOrder

import Control.Monad.Free

public export
data Out cnt = MkOut String cnt

public export
Functor Out where
  map f (MkOut x y) = MkOut x (f y)

public export
HOut : (Type -> Type) -> (Type -> Type)
HOut = Lift Out

public export
runOut : Free HOut a -> IO a
runOut (Return x) = pure x
runOut (Op (MkLift (MkOut s p))) =
  putStrLn s `io_bind` \_ => runOut p

public export
out : Inj HOut sig => String -> Free sig ()
out x = inject {sub = HOut} $ MkLift $ MkOut x (return ())

