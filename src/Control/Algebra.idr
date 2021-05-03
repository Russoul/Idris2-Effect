module Control.Algebra

import public Control.HigherOrder
import public Control.Effect.Misc

public export
interface Monad m => Algebra sig m where
  alg : (f : Functor ctx)
     => ctx ()
     -> Handler ctx n m
     -> sig n a
     -> m (ctx a)

public export
send : Sub eff sig => Algebra sig m => eff m a -> m a
send eff = alg {sig} {ctx = id} () id (inj eff)
