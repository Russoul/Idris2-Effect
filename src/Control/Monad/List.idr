module Control.Monad.List

import Control.HigherOrder

import Control.Monad.Trans


public export
data ListM : (Type -> Type) -> (Type -> Type) where
  Nil : ListM m a
  (::) : a -> m (ListM m a) -> ListM m a

public export
0
ListT : (Type -> Type) -> (Type -> Type)
ListT m a = m (ListM m a)

namespace Semigroup

  export
  [ListT] Monad m => Semigroup (ListT m a) where
    xs <+> ys =
      case !xs of
        [] => ys -- No idea it can't find the instance automatically.
        (x :: xs) => pure $ x :: ((<+>) @{ListT} xs ys)

  export
  [ListM] Monad m => Semigroup (ListM m a) where
    [] <+> ys = ys
    (x :: xs) <+> ys = x :: (<+>) @{ListT} xs (pure ys)

  %hint export
  ListTSemigroup : Monad m => Semigroup (ListT m a)
  ListTSemigroup = Semigroup.ListT

namespace Monoid
  %hint
  export
  ListT : Monad m => Monoid (ListT m a)
  ListT = MkMonoid @{Semigroup.ListT} (pure [])

  %hint
  export
  ListM : Monad m => Monoid (ListM m a)
  ListM = MkMonoid @{Semigroup.ListM} []

namespace Functor
  mutual
    export
    [ListM] Functor m => Functor (ListM m) where
      map f [] = []
      map f (x :: xs) = f x :: map @{ListT} f xs

    export
    [ListT] Functor m => Functor (ListT m) where
      map f x = map (map @{ListM} f) x

namespace Applicative
  %hint export
  ListT : Monad m => Applicative (ListT m)
  ListT = MkApplicative @{Functor.ListT}
    (pure . (:: pure Nil))
    $
    \fs, ys =>
      case !fs of
        [] => pure []
        f :: fs => (<+>) @{Semigroup.ListT}
          (map @{Functor.ListT} f ys)
          ((<*>) @{Applicative.ListT} fs ys)

namespace Monad

  bind : Monad m => ListT m a -> (a -> ListT m b) -> ListT m b
  bind xs f = do
    case !xs of
      [] => pure []
      x :: xs => (<+>) @{ListT} (f x) (bind xs f)

  %hint export
  ListT : Monad m => Monad (ListT m)
  ListT = MkMonad @{Applicative.ListT}
    (bind {m})
    (flip (bind {m}) id)

namespace Alternative
  %hint public export
  ListT : Monad m => Alternative (ListT m)
  ListT = MkAlternative @{Applicative.ListT} (pure []) (\x, y => (<+>) @{ListT} x y)

export
MonadTrans ListT where
  lift = (>>= pure @{ListT})

export
runListT' : Monad m => ListT m a -> m (Maybe a)
runListT' x = do
  case !x of
    [] => pure Nothing
    x :: xs => pure (Just x)

export
runListT : Monad m => ListT m a -> m (List a)
runListT x = do
  case !x of
    [] => pure []
    x :: xs => map (x ::) (runListT xs)

export
liftList : Applicative m => List a -> ListT m a
liftList [] = pure []
liftList (x :: xs) = pure (x :: liftList xs)
