module Control.Effect.Misc

-- TODO
-- Some definitions from this file may be later
-- relocated to more suitable places.

namespace Functor
  public export
  [Id] Functor (\x => x) where
    map f x = f x

  %hint public export
  FunctorId : Functor (\x => x)
  FunctorId = Functor.Id

  public export
  [LeftPair] Functor (, s) where
    map f (x, y) = (f x, y)

  %hint public export
  FunctorLeftPair : Functor (, s)
  FunctorLeftPair = Functor.LeftPair

namespace Applicative
  public export
  [Id] Applicative (\x => x) where
    pure x = x
    f <*> x = f x

  %hint public export
  ApplicativeId : Applicative (\x => x)
  ApplicativeId = Applicative.Id

namespace Monad
  public export
  [Id] Monad (\x => x) where
    x >>= f = f x

  %hint public export
  MonadId : Monad (\x => x)
  MonadId = Monad.Id
