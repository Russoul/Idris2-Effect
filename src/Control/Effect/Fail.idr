module Control.Effect.Fail

import Control.EffectAlgebra
import Control.Monad.Maybe
import Control.Monad.Either

public export
data FailE : Type -> (Type -> Type) -> (Type -> Type) where
  Fail : e -> FailE e m a

export
Functor (\e => FailE e m a) where
  map f (Fail x) = Fail (f x)

||| Fail a computation.
public export
fail : Inj (FailE e) sig => Algebra sig m => e -> m a
fail x = send (Fail x)

public export
fromEither : Inj (FailE e) sig => Algebra sig m => Either e b -> m b
fromEither (Left err) = fail err
fromEither (Right x) = pure x

||| Given a transformation between two failure types `e'` and `e`,
||| run an effectful computation `act` in the context
||| with the transformed failure.
export
glueFail : {0 m : Type -> Type}
        -> {0 e : Type}
        -> (fail : Inj (FailE e) sig)
        => (e' -> e)
        -> ((err : Inj (FailE e') sig) => m a)
        -> m a
glueFail morph act = act @{f}
 where
  f : Inj (FailE e') sig
  f = MkInj $ \case Fail x => inj (Fail (morph x))

namespace Algebra
  public export
  [Maybe] Algebra sig m => Algebra (FailE e :+: sig) (MaybeT m) where
    alg ctx hdl (Inl (Fail x)) = nothing
    alg ctxx hdl (Inr other) =
      let fused = (~<~) {ctx2 = ctx} {m = MaybeT m} f hdl in
      MkMaybeT (alg {f = Functor.Compose} {ctx = Maybe . ctx} (Just ctxx) fused other)
     where
      f : forall a. Maybe (MaybeT m a) -> m (Maybe a)
      f Nothing = pure Nothing
      f (Just x) = runMaybeT x

  public export
  [Either] Algebra sig m => Algebra (FailE e :+: sig) (EitherT e m) where
    alg ctx hdl (Inl (Fail x)) = left x
    alg ctxx hdl (Inr other) =
      let fused = (~<~) {ctx2 = ctx} {m = EitherT e m} f hdl in
      MkEitherT (alg {f = Functor.Compose} {ctx = Either e . ctx} (Right ctxx) fused other)
     where
      f : forall a. Either e (EitherT e m a) -> m (Either e a)
      f (Left x) = pure (Left x)
      f (Right x) = runEitherT x
