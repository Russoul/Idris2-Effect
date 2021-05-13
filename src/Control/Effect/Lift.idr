module Control.Effect.Lift

import Control.EffectAlgebra

namespace Algebra
  public export
  [Lift] Monad m => Algebra (Lift m) m where
    alg ctxx hdl (MkLift x) = x >>= hdl . ( <$ ctxx)

  %hint public export
  HintLift : Monad m => Algebra (Lift m) m
  HintLift = Lift

||| Lift a computation to the underlying effect stack.
public export
lift : Monad n => Inj (Lift n) sig => Algebra sig m => n a -> m a
lift x = send {eff = Lift n} $ MkLift (map pure x)
