module Control.Effect.Fail

import Control.EffectAlgebra
import Control.Monad.Maybe

public export
data FailE : Type -> (Type -> Type) -> (Type -> Type) where
  Fail : e -> FailE e m a

||| Fail a computation.
public export
fail : Inj (FailE e) sig => Algebra sig m => e -> m a
fail x = send {sig} {eff = FailE e} (Fail x)

public export
Algebra sig m => Algebra (FailE e :+: sig) (MaybeT m) where
  alg ctx hdl (Inl (Fail x)) = nothing
  alg ctxx hdl (Inr other) =
    let fused = (~<~) {ctx2 = ctx} {m = MaybeT m} f hdl in
    MkMaybeT (alg {f = Functor.Compose} {ctx = Maybe . ctx} (Just ctxx) fused other)
   where
    f : forall a. Maybe (MaybeT m a) -> m (Maybe a)
    f Nothing = pure Nothing
    f (Just x) = runMaybeT x
