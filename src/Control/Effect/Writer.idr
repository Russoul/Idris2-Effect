module Control.Effect.Writer

import Control.Algebra

import Control.Monad.Writer

public export
data WriterE : Type -> (Type -> Type) -> Type -> Type where
  Tell : s -> WriterE s m ()

||| Successive writes overwrite the preceding state.
public export
[Overwrite] Algebra sig m => Algebra (WriterE s :+: sig) (WriterT s m) where
  alg ctx hdl (Inl (Tell s)) = MkWriterT \_ => pure (ctx, s)
  alg ctx hdl (Inr x) = MkWriterT \r => do
   res <- alg {m} ctx (map fst . (flip unWriterT r) . hdl) x
   pure (res, r)

||| Newer writes are concatenated from the left, via the `Monoid` instance.
public export
[ConcatLeft] Monoid s => Algebra sig m => Algebra (WriterE s :+: sig) (WriterT s m) where
  alg ctxx hdl (Inl (Tell s)) = MkWriterT \s' => pure (ctxx, (s <+> s'))
  alg ctxx hdl (Inr x) = MkWriterT \r => do
   -- hdl : Hander ctx n (WriterT s m)
   -- h : Handler (,s) (WriterT s m) m
   -- h ~<~ hdl : Handler ((, s) . ctx) n m
   res <- alg
     {f = Functor.Compose @{(FunLeftPair, %search)}}
     (ctxx, r) h x
   pure res
   where
    h : Handler ((,s) . ctx) n m
    h =
       (~<~) {g = FunLeftPair}
        {ctx1 = (,s), ctx2 = ctx}
        {l = n}
        {m = WriterT s m} {n = m} (uncurry unWriterT) hdl

public export
tell : Sub (WriterE w) sig => Algebra sig m => w -> m ()
tell s = send {sig} {eff = WriterE w} (Tell s)

