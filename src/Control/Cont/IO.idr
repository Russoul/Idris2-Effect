module Control.Cont.IO

import Control.HigherOrder

import Control.Monad.Free

public export
data HIO : (Type -> Type) -> (Type -> Type) where
  MkHIO : forall t. IO t -> (t -> m a) -> HIO m a

public export
HFunctor HIO where
  hmap f (MkHIO x k) = MkHIO x (f . k)

public export
Syntax HIO where
  emap f (MkHIO x k) = MkHIO x (f . k)

  weave f hdl (MkHIO x k) =
    MkHIO (map (\x => map (const x) f) x)
            (hdl . map k)

public export
runIO : Free HIO a -> IO a
runIO (Return x) = pure x
runIO (Op (MkHIO x k)) = x `io_bind` runIO . k

public export
io : Syntax sig => Sub HIO sig => IO a -> Free sig a
io x = inject {sub = HIO} (MkHIO x Return)
