module Control.Cont.Void

import Control.EffectAlgebra
import Control.HigherOrder

import Control.Monad.Free

public export
data VoidC1 : Type -> Type where

public export
VoidC : (Type -> Type) -> (Type -> Type)
VoidC = Lift VoidC1

public export
VoidE : (Type -> Type) -> (Type -> Type)
VoidE = Lift VoidC1

public export
Uninhabited (VoidC1 a) where
  uninhabited x impossible

public export
Functor VoidC1 where
  map f x impossible

public export
runVoidC : Free VoidC a -> a
runVoidC (Return x) = x
runVoidC (Op (MkLift x)) = absurd x

namespace Algebra
  public export
  [VoidE] (mon : Monad m) => Algebra VoidE m where
    alg ctx hdl (MkLift x) = absurd x

  %hint
  public export
  AlgebraVoidE : (mon : Monad m) => Algebra VoidE m
  AlgebraVoidE = Algebra.VoidE
