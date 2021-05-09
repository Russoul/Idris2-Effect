module Control.Effect.Reader

import Control.EffectAlgebra

import Control.Monad.Reader

||| Reader effect.
public export
data ReaderE : Type -> (Type -> Type) -> Type -> Type where
  Ask : ReaderE r m r

export
Functor (\r => ReaderE r m r) where
  map _ Ask = Ask

||| Read the value within a monadic context that supports it.
public export
ask : Inj (ReaderE r) sig => Algebra sig m => m r
ask = send {sig} {eff = ReaderE r} Ask

namespace Algebra
  ||| Apply the reader effect of the signature to the underlying monad,
  ||| resulting in the ReaderT transformer.
  public export
  [Reader] (al : Algebra sig m) => Algebra (ReaderE s :+: sig) (ReaderT s m) where
    alg ctx hdl (Inl Ask) = MkReaderT \s => pure (s <$ ctx)
    alg ctx hdl (Inr x) = MkReaderT \r => alg ctx (runReaderT r . hdl) x

  %hint public export
  HintReader : (al : Algebra sig m) => Algebra (ReaderE s :+: sig) (ReaderT s m)
  HintReader = Reader
