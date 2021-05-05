module Control.Cont.Thread

import Data.List

import Control.HigherOrder

import Control.Monad.Free

public export
data Thread : (Type -> Type) -> (Type -> Type) where
  Yield : m a -> Thread m a
  Fork : forall t. m t -> m a -> Thread m a

public export
HThread : (Type -> Type) -> (Type -> Type)
HThread = Thread

public export
yield : Inj Thread sig => Free sig ()
yield = inject $ Yield $ return ()

public export
fork : Inj Thread sig => Free sig a -> Free sig ()
fork d = inject $ Fork d $ return ()

public export
HFunctor Thread where
  hmap f (Yield x) = Yield (f x)
  hmap f (Fork x y) = Fork (f x) (f y)

public export
Syntax Thread where
  emap f (Yield p) = Yield (f p)
  emap f (Fork d p) = Fork d (f p)

  weave s hdl (Yield p) = Yield (hdl (map (const p) s))
  weave s hdl (Fork d p) = Fork (hdl (map (const d) s))
                                (hdl (map (const p) s))

public export
data Daemon : ((Type -> Type) -> (Type -> Type)) -> Type where
  MkDaemon : forall t. Free (Thread :+: sig) t -> Daemon sig

public export
data SThread : (f : (Type -> Type) -> (Type -> Type))
            -> Type
            -> Type where
  SYield : Free (Thread :+: sig) r -> SThread sig r
  SFork : Daemon sig -> Free (Thread :+: sig) r -> SThread sig r
  SActive : r -> SThread sig r

public export
Syntax sig => Functor (SThread sig) where
  map f (SActive x) = SActive (f x)
  map f (SYield p) = SYield (map f p)
  map f (SFork d p) = SFork d (map f p)

mutual
  public export
  thread : Syntax sig
        => Handler (SThread sig) (Free (Thread :+: sig)) (Free sig)
  thread (SActive p) = runThread p
  thread (SYield p) = return (SYield (join p))
  thread (SFork d p) = return (SFork d (join p))

  public export
  runThread : Syntax sig
           => Free (Thread :+: sig) a -> Free sig (SThread sig a)
  runThread (Return x) = return (SActive x)
  runThread (Op (Inl (Yield q))) = return (SYield q)
  runThread (Op (Inl (Fork d q))) = return (SFork (MkDaemon d) q)
  runThread (Op (Inr op)) = Op (weave {s = SThread sig} (SActive ()) thread op)

public export
schedule : Syntax sig => Free (Thread :+: sig) a -> Free sig a
schedule p = master p [] where
  mutual
    daemons : List (Daemon sig) -> List (Daemon sig) -> Free (Thread :+: sig) a -> Free sig a
    daemons [] ds' p = master p (reverse ds')
    daemons (MkDaemon q :: ds) ds' p = do
      r <- runThread q
      case r of
        SActive _ => daemons ds ds' p
        SYield q' => daemons ds (MkDaemon q' :: ds') p
        SFork d' q' => daemons (d' :: ds) (MkDaemon q' :: ds') p

    master : Free (Thread :+: sig) a -> List (Daemon sig) -> Free sig a
    master p ds = do
      r <- runThread p
      case r of
        SActive x => return x
        SYield p => daemons ds [] p
        SFork d p => daemons (d :: ds) [] p
