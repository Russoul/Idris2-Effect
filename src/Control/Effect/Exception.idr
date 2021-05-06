module Control.Effect.Exception

import Control.EffectAlgebra

import Control.Monad.Either

||| Exception effect.
public export
data EitherE : Type -> (Type -> Type) -> Type -> Type where
  Fail : e -> EitherE e m a
  Try : m a -> (e -> m a) -> EitherE e m a

||| Fail a computation.
public export
fail : Inj (EitherE e) sig => Algebra sig m => e -> m a
fail x = send {sig} {eff = EitherE e} (Fail x)

||| Try running a computation. If it fails (via Fail) resort to the supplied callback.
public export
try : Inj (EitherE e) sig => Algebra sig m => m a -> (e -> m a) -> m a
try x err = send {sig} {eff = EitherE e} (Try x err)

public export
fromEither : Inj (EitherE e) sig => Algebra sig m => Either e b -> m b
fromEither (Left err) = fail {sig} err
fromEither (Right x) = pure x

namespace Algebra
  public export
  [Either] (al : Algebra sig m) => Algebra (EitherE e :+: sig) (EitherT e m) where
    alg ctx hdl (Inl (Fail x)) = left x
    alg ctx hdl (Inl (Try t er)) =
      catchE (hdl (t <$ ctx)) (hdl . (<$ ctx) . er)
    alg ctxx hdl (Inr other) =
      let fused = (~<~) {ctx2 = ctx} {m = EitherT e m} f hdl in
      MkEitherT (alg {f = Functor.Compose} {ctx = Either e . ctx} (Right ctxx) fused other)
     where
      f : forall a. Either e (EitherT e m a) -> m (Either e a)
      f (Left x) = pure (Left x)
      f (Right x) = runEitherT x

  %hint public export
  AlgebraEither : (al : Algebra sig m) => Algebra (EitherE e :+: sig) (EitherT e m)
  AlgebraEither = Algebra.Either
