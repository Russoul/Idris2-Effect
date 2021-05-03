module Control.HigherOrder

infixr 0 ~>
infixr 0 ~~>

||| Type of natural transformations between two functors.
public export
0
(~>) : (Type -> Type) -> (Type -> Type) -> Type
f ~> g = forall a. f a -> g a

public export
0
(~~>) : (Type -> Type) -> (Type -> Type) -> (Type -> Type)
(f ~~> g) a = f a -> g a

||| Higher-order functor, i.e. a functor
||| in the category of functors and natural transformations.
public export
interface HFunctor h where
  hmap : (Functor f, Functor g)
      =>   f ~>   g
      -> h f ~> h g

infixr 8 :+:

||| Higher-order disjoint union.
public export
data (:+:) : (sig1 : (Type -> Type) -> (Type -> Type))
          -> (sig2 : (Type -> Type) -> (Type -> Type))
          -> (m : Type -> Type)
          -> (a : Type)
          -> Type where
  Inl : sig1 m a -> (:+:) sig1 sig2 m a
  Inr : sig2 m a -> (:+:) sig1 sig2 m a

public export
HFunctor sig1 => HFunctor sig2 => HFunctor (sig1 :+: sig2) where
  hmap t (Inl op) = Inl (hmap t op)
  hmap t (Inr op) = Inr (hmap t op)

public export
interface Sub (0 sub : (Type -> Type) -> (Type -> Type))
              (0 sup : (Type -> Type) -> (Type -> Type)) | sub where
  constructor MkSub
  inj : sub m a -> sup m a
  prj : sup m a -> Maybe (sub m a)

namespace Sub
  public export
  [S] Sub sig sig where
     inj = id
     prj = Just

  public export
  [T] Sub siga sigb => Sub sigb sigc => Sub siga sigc where
    inj = inj {sub = sigb} {sup = sigc} . inj
    prj = prj {sub = siga} {sup = sigb} <=< prj

  public export
  [L] Sub sig1 (sig1 :+: sig2) where
    inj = Inl
    prj (Inl fa) = Just fa
    prj _ = Nothing

  public export
  [R] Sub sig2 (sig1 :+: sig2) where
    inj = Inr
    prj (Inr fa) = Just fa
    prj _ = Nothing

||| State-preserving transformation of
||| a computation in one monad into a computation
||| in another monad, whose value is annotated with the final state.
||| Handler is a natural transformation.
public export
0
Handler : (Type -> Type)
       -> (Type -> Type)
       -> (Type -> Type)
       -> Type
Handler s m n = s . m ~> n . s

public export
0
HandlerX : (Type -> Type)
        -> (Type -> Type)
        -> (Type -> Type)
        -> (Type -> Type)
HandlerX s m n = s . m ~~> n . s

public export
interface HFunctor sig => Syntax sig where
  ||| Extend the continuation.
  emap : forall m. (m a -> m b) -> (sig m a -> sig m b)
  ||| Generically thread a handler through a higher-order
  ||| signature.
  weave : (m1 : Monad m) => (m2 : Monad n) => (fs : Functor s)
       => s ()
       -> Handler s m n
       -> (sig m a -> sig n (s a))

public export
Syntax sig1 => Syntax sig2 => Syntax (sig1 :+: sig2) where
  emap f (Inl op) = Inl (emap f op)
  emap f (Inr op) = Inr (emap f op)

  weave s hdl (Inl op) = Inl (weave s hdl op)
  weave s hdl (Inr op) = Inr (weave s hdl op)

-- Lift a first-order functor to a higher-order one.
public export
data Lift : (sig : (Type -> Type))
         -> ((Type -> Type) -> (Type -> Type)) where
  MkLift : sig (m a) -> Lift sig m a

public export
Functor sig => HFunctor (Lift sig) where
  hmap t (MkLift op) = MkLift (map t op)

public export
Functor sig => Syntax (Lift sig) where
  emap f (MkLift op) = MkLift (map f op)

  weave s hdl (MkLift op) = MkLift $
    map (\p => hdl (map (const p) s)) op

-- hdl1 : ctxt1 . m ~> n . ctxt1
-- hdl2 : ctxt2 . l ~> m . ctxt2
-- ?    : (ctxt1 . ctxt2) . l ~> n . (ctxt1 . ctxt2)
--
--  (ctxt1 . ctxt2) . l ===
--  ctxt1 . (ctxt2 . l) ==>
--  ctxt1 . (m . ctxt2) ===
--  (ctxt1 . m) . ctxt2 ==>
--  (n . ctxt1) . ctxt2 ===
--  n . (ctxt1 . ctxt2)
infixr 1 ~<~
||| Fuse two handlers.
public export
(~<~) : (f : Functor n)
     => (g : Functor ctx1)
     => (forall q. HandlerX ctx1 m n q)
     -> (forall t. HandlerX ctx2 l m t)
     -> (forall p. HandlerX (ctx1 . ctx2) l n p)
hdl1 ~<~ hdl2 = hdl1 . map hdl2

