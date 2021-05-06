module Control.EffectAlgebra

import public Control.HigherOrder
import public Control.Effect.Misc

||| Structure that dispatches an effect.
public export
interface Monad m => Algebra sig m where
  constructor MkAlgebra
  alg : (f : Functor ctx)
     => ctx ()
     -> Handler ctx n m
     -> sig n a
     -> m (ctx a)

||| Apply an effect within a monadic context that supports it.
public export
send : Inj eff sig => Algebra sig m => eff m a -> m a
send eff = alg {sig} {ctx = id} () id (inj eff)
