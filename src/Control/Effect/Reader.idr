module Control.Effect.Reader

import Control.Algebra

import Control.Monad.Reader

||| Reader effect.
public export
data ReaderE : Type -> (Type -> Type) -> Type -> Type where
  Ask : ReaderE s m s

public export
ask : Sub (ReaderE r) sig => Algebra sig m => m r
ask = send {sig} {eff = ReaderE r} Ask

||| Apply the reader effect of the signature to the underlying monad,
||| resulting in the ReaderT transformer.
public export
Algebra sig m => Algebra (ReaderE s :+: sig) (ReaderT s m) where
  alg ctx hdl (Inl Ask) = MkReaderT \s => pure (s <$ ctx)
  alg ctx hdl (Inr x) = MkReaderT \r => alg ctx (runReaderT r . hdl) x
