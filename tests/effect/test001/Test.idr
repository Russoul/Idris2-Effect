module Test

import Data.List
import Data.Vect
import Data.Either
import Data.Maybe
import Data.String
import Data.Ref
import Control.Monad.Reader
import Control.Monad.Writer
import Control.Monad.Either
import Control.Monad.Identity
import Control.Monad.Free
import Control.Monad.State

import Control.EffectAlgebra
import Control.Effect.Exception
import Control.Effect.Labelled
import Control.Effect.Lift
import Control.Effect.Reader
import Control.Effect.Writer
import Control.Effect.State
import Control.Cont.Void
import Control.Cont.State
import Control.Cont.Thread
import Control.Cont.Out
import Control.Cont.IO
import Control.Cont.Exception

-------------------------------------
throwSnapshot : (Syntax sig, Inj (EitherC (e, s)) sig, Inj (StateC s) sig) => e -> Free sig a
throwSnapshot err = do
  v <- Cont.State.get {s}
  throw (err, v)

decr : (Syntax sig, Inj (StateC Int) sig, Inj (EitherC ()) sig) => Free sig ()
decr = do
  x <- Cont.State.get {s = Int}
  if x > 0 then Cont.State.put (x - 1)
     else throw ()

incrC : (Syntax sig, Inj (StateC Int) sig) => Free sig ()
incrC = do
  x <- Cont.State.get {s = Int}
  Cont.State.put (x + 1)

testStateExc : Syntax sig
           => (s : Inj (StateC Int) sig)
           => (e : Inj (EitherC (String, Int)) sig)
           => Free sig (String, Int)
testStateExc = do
  catch {e = (String, Int)} (incrC >> throwSnapshot {s = Int} "thrown") \(str, i) => do
    incrC >> return (str ++ "-return", i + 22)

testStateExcRun : Either (String, Int) (Int, (String, Int))
testStateExcRun = runVoidC . runEitherC . runStateC 3 $ testStateExc
  {e = T @{L} @{R}}
  {s = L}

-------------------------------------

tripleDecr : Syntax sig => (s : Inj (StateC Int) sig) => (e : Inj (EitherC ()) sig) => Free sig ()
tripleDecr = decr >> catch (decr >> decr) return

tripleDecrInst : Free (StateC Int :+: (EitherC () :+: VoidE)) ()
tripleDecrInst = tripleDecr
  {e = MkInj (Inr . Inl)}
  {s = MkInj Inl}

tripleDecrInst' : Free (EitherC () :+: (StateC Int :+: VoidE)) ()
tripleDecrInst' = tripleDecr
  {e = MkInj Inl}
  {s = MkInj (Inr . Inl)}

runLocal : Either () (Int, ())
runLocal = runVoidC . runEitherC . runStateC 2 $ tripleDecrInst

runGlobal : (Int, Either () ())
runGlobal = runVoidC . runStateC 2 . runEitherC $ tripleDecrInst'

-----------------------

%hide Control.Monad.Writer.Interface.tell
%hide Control.Monad.Reader.Interface.ask

testFused : (a : Algebra sig m)
      => (r : Inj (ReaderE Nat) sig)
      => (w : Inj (WriterE (List Nat)) sig)
      => m String
testFused = do
  x <- ask {r = Nat}
  tell {w = List Nat} [x + 1]
  tell {w = List Nat} [x + 3, x + 2]
  pure "Done"

%hint
MyWriter : Monoid s => Algebra sig m => Algebra (WriterE s :+: sig) (WriterT s m)
MyWriter = ConcatLeft

handleFused : ReaderT Nat (WriterT (List Nat) Identity) String
handleFused = testFused {sig = ReaderE Nat :+: WriterE (List Nat) :+: VoidE}
               {r = L}
               {w = T @{L} @{R}}

runFused : List Nat
runFused = runIdentity . map snd . runWriterT . runReaderT 20 $ handleFused

-----------------------

testEitherE : (a : Algebra sig m)
           => (r : Inj (ReaderE Nat) sig)
           => (w : Inj (WriterE (List Nat)) sig)
           => (e : Inj (EitherE String) sig)
           => (toThrow : Bool)
           -> m String
testEitherE toThrow = do
  x <- ask {r = Nat}
  tell {w = List Nat} [1, x]
  tell {w = List Nat} [3, 2]
  r <- try {e = String}
        (do tell {w = List Nat} [6, 5, 4]
            if toThrow then fail "fail" else pure "pure")
    (\er => pure "on throw")
  pure r

handleEitherE : Bool -> (WriterT (List Nat) $ ReaderT Nat $ EitherT String Identity) String
handleEitherE x = testEitherE x {sig = WriterE (List Nat) :+: ReaderE Nat :+: EitherE String :+: VoidE}
                  {w = L}
                  {r = T @{L} @{R}}
                  {e = T @{T @{L} @{R}} @{R}}

runEitherE : Bool -> Either String (String, List Nat)
runEitherE x = runIdentity . runEitherT . runReaderT 0 . runWriterT $ handleEitherE x

-----------------------

readerSum : (rx : InjL "x" (ReaderE Int) sig)
         => (ry : InjL "y" (ReaderE Int) sig)
         => (al : Algebra sig m)
         => m Int
readerSum = do
  a <- labelled "x" Ask
  b <- labelled "y" Ask
  pure (a + b)

runReaderSum : Int
runReaderSum =
  runIdentity . runReaderT 1 . runReaderT 2 $ readerSum
  {sig = ReaderE Int :+: ReaderE Int :+: VoidE}
  {rx = Label @{L}}
  {ry = Label @{T @{L} @{R}}}
  {al = the (Algebra _ $ ReaderT Int (ReaderT Int Identity)) %search}

-----------------------

testWriterIO : (r : Inj (ReaderE Int) sig)
            => (io : Inj (Lift IO) sig)
            => (al : Algebra sig m)
            => m ()
testWriterIO = do
  x <- ask {r = Int}
  lift {n = IO} (putStrLn (show x))

runTestWriterIO : IO ()
runTestWriterIO = runReaderT 2 $ testWriterIO
  {sig = ReaderE Int :+: Lift IO}
  {r = L}
  {io = R}
  {al = the (Algebra _ $ ReaderT Int IO) %search}

-----------------------

incrE : (s : Inj (StateE Int) sig)
     => (al : Algebra sig m)
     => m ()
incrE = do
  x <- Effect.State.get {s = Int}
  Effect.State.put (x + 1)

runIncr : Int
runIncr = runIdentity . map fst . runStateT 0 $ incrE
  {sig = StateE Int :+: VoidE}
  {s = L}
  {al = the (Algebra _ $ StateT Int Identity) %search}

-----------------------

main : IO ()
main = pure ()
