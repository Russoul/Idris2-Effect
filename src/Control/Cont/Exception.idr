module Control.Cont.Exception

import Control.EffectAlgebra

import Control.Monad.Free

public export
data EitherC : Type -> (Type -> Type) -> Type -> Type where
  Throw : e -> EitherC e m a
  Catch : forall t. m t -> (e -> m t) -> (t -> m a) -> EitherC e m a

public export
Functor m => Functor (EitherC e m) where
  map f (Throw e) = Throw e
  map f (Catch p h k) = Catch p h (map f . k)

public export
HFunctor (EitherC e) where
  hmap t (Throw x) = Throw x
  hmap t (Catch p h k) = Catch (t p) (t . h) (t . k)

public export
Syntax (EitherC e) where
  emap f (Throw e) = Throw e
  emap f (Catch p h k) = Catch p h (f . k)

  weave f hdl (Throw x) = Throw x
  weave f hdl (Catch p h k) =
    Catch (hdl (map (const p) f))
          (\e => hdl (map (const (h e)) f))
          (hdl . map k)

public export
runEitherC : Syntax sig
      => Free (EitherC e :+: sig) a
      -> Free sig (Either e a)
runEitherC (Return x) = Return (Right x)
runEitherC (Op (Inl (Throw x))) = Return (Left x)
runEitherC (Op (Inl (Catch p h k))) = do
  r <- runEitherC p
  case r of
    Left e => do
      r <- runEitherC (h e)
      case r of
        Left e => Return (Left e)
        Right x => runEitherC (k x)
    Right x => runEitherC (k x)
runEitherC (Op (Inr op)) = Op (weave {s = Either e} (Right ()) hdl op) where
  hdl : Handler (Either e) (Free (EitherC e :+: sig)) (Free sig)
  hdl = either (Return . Left) runEitherC

public export
throw : (Sub (EitherC e) sig) => e -> Free sig a
throw err = inject {sub = EitherC e} (Throw err)

public export
catch : (p : Sub (EitherC e) sig) => Free sig a -> (e -> Free sig a) -> Free sig a
catch p h = inject {sub = EitherC e} (Catch p h Return)

public export
orThrow : Syntax sig => Sub (EitherC e) sig => Maybe a -> Free sig e -> Free sig a
orThrow Nothing e  = e >>= throw
orThrow (Just x) e = return x
