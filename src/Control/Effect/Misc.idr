module Control.Effect.Misc

-- TODO
-- Some definitions from this file may be later
-- relocated to more suitable places.

namespace Functor
  public export
  Functor (\x => x) where
   map f x = f x

  public export
  [LeftPair] Functor (, s) where
    map f (x, y) = (f x, y)

