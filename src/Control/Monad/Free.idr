module Control.Monad.Free

import Control.Algebra

||| Higher-order free monad.
||| Acts as a syntax generator of effectful programs.
public export
data Free : (sig : (Type -> Type) -> (Type -> Type))
         -> Type
         -> Type where
  Return : a -> Free sig a
  Op : sig (Free sig) a -> Free sig a

public export
Syntax sig => Functor (Free sig) where
  map f (Return x) = Return (f x)
  map f (Op op)    = Op (emap (map f) op)

public export
Syntax sig => Applicative (Free sig) where
  pure v = Return v

  Return v <*> prog = map v prog
  Op op    <*> prog = Op (emap (<*> prog) op)

public export
Syntax sig => Monad (Free sig) where
  Return v >>= prog = prog v
  Op op    >>= prog = Op (emap (>>= prog) op)

public export
return : a -> Free sig a
return = Return

public export
inject : Sub sub sup => sub (Free sup) a -> Free sup a
inject = Op . inj

public export
project : Sub sub sup => Free sup a -> Maybe (sub (Free sup) a)
project (Op s) = prj s
project _ = Nothing

