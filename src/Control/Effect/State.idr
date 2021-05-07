module Control.Effect.State

import Control.EffectAlgebra
import Control.HigherOrder

import Control.Monad.State

import public Control.Effect.Reader
import public Control.Effect.Writer

||| State effect - the union of Reader and Writer effects.
public export
StateE : Type -> (Type -> Type) -> (Type -> Type)
StateE s = ReaderE s :+: WriterE s

public export
Inj (StateE s) sig => Inj (ReaderE s) sig where
  inj = inj {sub = StateE s, sup = sig} . Inl

public export
Inj (StateE s) sig => Inj (WriterE s) sig where
  inj = inj {sub = StateE s, sup = sig} . Inr

-- public export
-- get : Algebra sig m => Inj (StateE s) sig => m s
-- get = send {sig} {eff = StateE s} (Inl Ask)

-- public export
-- put : Algebra sig m => Inj (StateE s) sig => s -> m ()
-- put x = send {sig} {eff = StateE s} (Inr (Tell x))

namespace Algebra
  public export
  [State] Algebra sig m => Algebra (StateE s :+: sig) (StateT s m) where
    alg ctxx hdl (Inl (Inl Ask)) =
      ST \s => pure {f = m} (s, (s <$ ctxx))
    alg ctxx hdl (Inl (Inr (Tell s))) =
      ST \_ => pure {f = m} (s, ctxx)
    alg ctxx hdl (Inr x) = ST \r => do
     res <- alg
       {f = Functor.Compose}
       (r, ctxx) h x
     pure res
     where
      h : Handler ((s,) . ctx) n m
      h =
         (~<~)
          {ctx1 = (s,), ctx2 = ctx}
          {l = n}
          {m = StateT s m} {n = m} (uncurry runStateT) hdl

  %hint public export
  HintState : Algebra sig m => Algebra (StateE s :+: sig) (StateT s m)
  HintState = State
