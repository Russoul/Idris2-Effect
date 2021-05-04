module Control.Effect.Lift

import Control.Algebra

public export
Monad m => Algebra (Lift m) m where
  alg ctxx hdl (MkLift x) = x >>= hdl . ( <$ ctxx)

public export
lift : Monad n => Sub (Lift n) sig => Algebra sig m => n a -> m a
lift x = send {eff = Lift n} {sig} $ MkLift (map pure x)
