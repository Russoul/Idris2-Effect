module Control.Cont.State

import Control.HigherOrder

import Control.Monad.Free

public export
data StateC1 : Type -> Type -> Type where
  Get : (s -> x) -> StateC1 s x
  Put : s -> x -> StateC1 s x

public export
Functor (StateC1 s) where
  map f (Get g) = Get (f . g)
  map f (Put s x) = Put s (f x)

public export
StateC : Type -> (Type -> Type) -> Type -> Type
StateC s = Lift (StateC1 s)

public export
runStateC : Syntax sig
         => s
         -> Free (StateC s :+: sig) a
         -> Free sig (s, a)
runStateC s (Return x) = Return (s, x)
runStateC s (Op (Inl (MkLift (Get k)))) =
  runStateC s (k s)
runStateC s (Op (Inl (MkLift (Put s' k)))) =
  runStateC s' k
runStateC s (Op (Inr op)) =
  Op (weave {m1 = ?t} {s = Pair _} (s, ()) (uncurry runStateC) op)

public export
get : (Inj (StateC s) sig) => Free sig s
get = inject {sub = StateC s} (MkLift (Get Return))

public export
put : (Inj (StateC s) sig) => s -> Free sig ()
put val = inject {sub = StateC s} (MkLift (Put val (Return ())))

public export
modify : Syntax sig => Inj (StateC s) sig => (s -> s) -> Free sig ()
modify f = do
  v <- get
  put (f v)

public export
withSt : Syntax sig => Inj (StateC st) sig => a -> Free sig (st, a)
withSt x = map (, x) get

