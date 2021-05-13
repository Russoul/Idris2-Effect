module Control.Effect.Exception

import Data.Contravariant

import Control.EffectAlgebra

import public Control.Effect.Fail

import Control.Monad.Either

||| Exception effect.
public export
data TryE : Type -> (Type -> Type) -> Type -> Type where
  Try : m a -> (e -> m a) -> TryE e m a

public export
Contravariant (\e => TryE e m r) where
  contramap f (Try x h) = Try x (h . f)

public export
EitherE : Type -> (Type -> Type) -> Type -> Type
EitherE e = TryE e :+: FailE e

public export
Inj (EitherE e) sig => Inj (FailE e) sig where
  inj = inj {sub = EitherE e, sup = sig} . Inr

public export
Inj (EitherE e) sig => Inj (TryE e) sig where
  inj = inj {sub = EitherE e, sup = sig} . Inl

||| Try running a computation. If it fails (via Fail) resort to the supplied callback.
public export
try : Inj (TryE e) sig => Algebra sig m => m a -> (e -> m a) -> m a
try x err = send (Try x err)

namespace Algebra
  public export
  [Either] (al : Algebra sig m) => Algebra (EitherE e :+: sig) (EitherT e m) where
    alg ctx hdl (Inl (Inr (Fail x))) = left x
    alg ctx hdl (Inl (Inl (Try t er))) =
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
