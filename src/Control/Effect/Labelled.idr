module Control.Effect.Labelled

import Control.EffectAlgebra

public export
data Labelled : (label : k)
             -> (sub : (Type -> Type) -> (Type -> Type))
             -> (m : Type -> Type) -> (Type -> Type) where
  MkLabelled : (eff : sub m a) -> Labelled label sub m a

public export
runLabelled : Labelled label sub m a -> sub m a
runLabelled (MkLabelled eff) = eff

public export
Functor (sub m) => Functor (Labelled label sub m) where
  map f (MkLabelled x) = MkLabelled (map f x)

public export
Applicative (sub m) => Applicative (Labelled label sub m) where
  pure x = MkLabelled (pure x)

  (MkLabelled f) <*> (MkLabelled x) = MkLabelled (f <*> x)

public export
Monad (sub m) => Monad (Labelled label sub m) where
  (MkLabelled x) >>= f = MkLabelled (x >>= runLabelled . f)

public export
Algebra (eff :+: sig) (sub m)
  => Algebra (Labelled label eff :+: sig)
             (Labelled label sub m) where
  alg ctxx hdl (Inl (MkLabelled x)) = MkLabelled $
    alg {sig = eff :+: sig, m = sub m}
        ctxx (runLabelled . hdl) (Inl x)
  alg ctxx hdl (Inr x) = MkLabelled $
    alg {sig = eff :+: sig, m = sub m}
        ctxx (runLabelled . hdl) (Inr x)

public export
interface InjL (0 label : k)
               (0 sub : (Type -> Type) -> (Type -> Type))
               (0 sup : (Type -> Type) -> (Type -> Type)) | label where
  constructor MkSubL
  injLabelled : Labelled label sub m a -> sup m a

public export
[LabelAuto] Inj sub sup => InjL label sub sup where
  injLabelled (MkLabelled x) = inj x

public export
Label : Inj sub sup -> InjL label sub sup
Label x = LabelAuto @{x}

public export
labelled : (label : k)
        -> InjL label sub sig
        => Algebra sig m
        => sub m a -> m a
labelled label @{sub} x =
  let y = injLabelled (MkLabelled {label} x) in
  alg {ctx = id} () id y
