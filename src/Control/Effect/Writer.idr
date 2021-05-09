module Control.Effect.Writer

import Control.EffectAlgebra

import Control.Monad.Writer

||| Writer effect.
public export
data WriterE : Type -> (Type -> Type) -> Type -> Type where
  Tell : w -> WriterE w m ()

export
Functor (\w => WriterE w m a) where
  map f (Tell x) = Tell (f x)

||| Write the value to the context within a monadic computation that supports it.
public export
tell : Inj (WriterE w) sig => Algebra sig m => w -> m ()
tell s = send {sig} {eff = WriterE w} (Tell s)

namespace Algebra
  ||| Successive writes overwrite the preceding state.
  public export
  [Overwrite] Algebra sig m => Algebra (WriterE s :+: sig) (WriterT s m) where
    alg ctx hdl (Inl (Tell s)) = MkWriterT \_ => pure (ctx, s)
    alg ctxx hdl (Inr x) = MkWriterT \r => do
     res <- alg
       {f = Functor.Compose @{(Functor.LeftPair, %search)}}
       (ctxx, r) h x
     pure res
     where
      h : Handler ((,s) . ctx) n m
      h =
         (~<~) {g = Functor.LeftPair}
          {ctx1 = (,s), ctx2 = ctx}
          {l = n}
          {m = WriterT s m} {n = m} (uncurry unWriterT) hdl

  ||| Newer writes are concatenated from the left, via the `Monoid` instance.
  public export
  [ConcatLeft] Monoid s => Algebra sig m => Algebra (WriterE s :+: sig) (WriterT s m) where
    alg ctxx hdl (Inl (Tell s)) = MkWriterT \s' => pure (ctxx, (s <+> s'))
    alg ctxx hdl (Inr x) = MkWriterT \r => do
     -- hdl : Hander ctx n (WriterT s m)
     -- h : Handler (,s) (WriterT s m) m
     -- h ~<~ hdl : Handler ((, s) . ctx) n m
     res <- alg
       {f = Functor.Compose @{(Functor.LeftPair, %search)}}
       (ctxx, r) h x
     pure res
     where
      h : Handler ((,s) . ctx) n m
      h =
         (~<~) {g = Functor.LeftPair}
          {ctx1 = (,s), ctx2 = ctx}
          {l = n}
          {m = WriterT s m} {n = m} (uncurry unWriterT) hdl
