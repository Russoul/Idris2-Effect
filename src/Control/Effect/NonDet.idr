module Control.Effect.NonDet

import Control.EffectAlgebra

import Control.Monad.List

import Data.List1

||| Add non-determinism to a computation,
||| e.i. alternatives for program flow.
||| Choice between these alternatives is not directly specified and is
||| deferred to a particular handler.
public export
data ChoiceE : (Type -> Type) -> (Type -> Type) where
  Choose : List (m a) -> ChoiceE m a

namespace Algebra
  alg :   Algebra sig m
       => (f : Functor ctx)
       => ctx ()
       -> Handler ctx n (ListT m)
     -> (ChoiceE :+: sig) n a
     -> (ListT m) (ctx a)
  alg ctxx hdl (Inl (Choose list)) =
    go list
   where
    go : List (n a) -> ListT m (ctx a)
    go [] = pure []
    go (x :: xs) = (<+>) @{ListT} (hdl (x <$ ctxx)) (go xs)
  alg ctxx hdl (Inr other) =
    -- hdl : Handler ctx n (ListT m)
    -- hdl' : Handler (List m) (ListT m) m
    -- ? : Handler (List m . ctx) n m
    EffectAlgebra.alg {f = Functor.Compose @{(ListM, %search)}}
        {ctx = ListM m . ctx}
        {m} (ctxx :: pure [])
        ((~<~) @{%search} @{Functor.ListM} { ctx1 = ListM m
               , ctx2 = ctx
               , l = n
               , m = ListT m
               , n = m} f hdl) other
   where
    f : Handler (ListM m) (ListT m) m
    f = join @{Monad.ListT} . pure

  ||| Handle choice by accumulating all alternatives in a list transformer.
  %hint export
  Concat : (al : Algebra sig m) => Algebra (ChoiceE :+: sig) (ListT m)
  Concat = MkAlgebra @{Monad.ListT} Algebra.alg

||| Introduce non-deterministic branching to a computation.
public export
oneOf : Inj ChoiceE sig
     => Algebra sig m
     => List a
     -> m a
oneOf list =
  send {eff = ChoiceE} (Choose (map pure list))

||| Introduce non-deterministic branching to a computation.
public export
oneOfM : Inj ChoiceE sig
     => Algebra sig m
     => List (m a)
     -> m a
oneOfM list =
  send {eff = ChoiceE} (Choose list)
