module Test

import Data.List
import Data.Vect
import Data.Either
import Data.Maybe
import Data.String
import Data.Ref
import Data.Stream
import Control.Monad.Reader
import Control.Monad.Writer
import Control.Monad.Either
import Control.Monad.Identity
import Control.Monad.Free
import Control.Monad.State
import Control.Monad.List

import Control.EffectAlgebra
import Control.Effect.Exception
import Control.Effect.Labelled
import Control.Effect.Lift
import Control.Effect.Reader
import Control.Effect.Writer
import Control.Effect.State
import Control.Effect.NonDet
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
  {e = T L R}
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

testFused : (al : Algebra sig m)
         => (r : Inj (ReaderE Nat) sig)
         => (w : Inj (WriterE (List Nat)) sig)
         => m String
testFused = do
  x <- ask {r = Nat}
  tell {w = List Nat} [x + 1]
  tell {w = List Nat} [x + 3, x + 2]
  pure "Done"

handleFused : ReaderT Nat (WriterT (List Nat) Identity) String
handleFused = testFused {sig = ReaderE Nat :+: WriterE (List Nat) :+: VoidE}
               {r = L}
               {w = T L R}
               {al = Reader.Algebra.Reader
                      @{Writer.Algebra.ConcatLeft}}

runFused : List Nat
runFused = runIdentity . map snd . runWriterT . runReaderT 20 $ handleFused

-----------------------

testEitherE : (al : Algebra sig m)
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
            if toThrow then fail {sig} "fail" else pure "pure")
    (\er => pure "on throw")
  pure r

handleEitherE : Bool -> (WriterT (List Nat) $ ReaderT Nat $ EitherT String Identity) String
handleEitherE x = testEitherE x
  {sig = WriterE (List Nat) :+: ReaderE Nat :+: EitherE String :+: VoidE}
  {w = L}
  {r = T L R}
  {e = T (T L R) R}
  {al = Algebra.ConcatLeft @{%search} @{Algebra.Reader @{Algebra.Either}}}

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
  {rx = Label L}
  {ry = Label (T L R)}
  {al = Reader @{Reader}}

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
  {al = Reader}

-----------------------

incrE : (s : Inj (StateE Int) sig)
     => (al : Algebra sig m)
     => m ()
incrE = do
  x <- ask {sig} {r = Int}
  tell {sig} (x + 1)

runIncr : Int
runIncr = runIdentity . map fst . runStateT 0 $ incrE
  {sig = StateE Int :+: VoidE}
  {s = L}
  {al = State}

-----------------------

standaloneList : (l : Inj ChoiceE sig)
              => (al : Algebra sig m)
              => m (Int, Int)
standaloneList = do
  x <- oneOf ([1, 2, 3, 4])
  y <- oneOf ([5, 6, 7, 8])
  pure (x, y)

runStandaloneList : List (Int, Int)
runStandaloneList = runIdentity . runListT $ standaloneList
  {sig = ChoiceE :+: VoidC}
  {l = L}
  {al = Algebra.Concat}

-----------------------

%hide Trans.lift

tooBig : (l : Inj ChoiceE sig)
      => (e : Inj (EitherE Int) sig)
      => (al : Algebra sig m)
      => List Int
      -> m Int
tooBig list = do
  v <- oneOf list
  if v > 5 then fail {sig} {e = Int} v else pure v

tooBigCatch : (l : Inj ChoiceE sig)
           => (e : Inj (EitherE Int) sig)
           => (al : Algebra sig m)
           => List Int
           -> m Int
tooBigCatch list = do
  v <- oneOf list
  try (if v > the Int 5 then fail {sig} {e = Int} v else pure v)
   \v => if v > the Int 7 then fail {sig} {e = Int} v else pure v

runTooBig : ?
runTooBig = runIdentity . runListT' . runEitherT $ tooBig [5, 7, 1]
 {sig = EitherE Int :+: ChoiceE :+: VoidE}
 {e = L}
 {l = T L R}
 {al = Algebra.Either @{Algebra.Concat}}

runTooBig' : ?
runTooBig' = runIdentity . runEitherT . runListT $ tooBig [5, 7, 1]
 {sig =  ChoiceE :+: EitherE Int :+: VoidE}
 {l = L}
 {e = T L R}
 {al = Algebra.Concat @{Algebra.Either}}

runTooBigCatch : ?
runTooBigCatch = runIdentity . runListT . runEitherT $ tooBigCatch [5, 7, 1]
 {sig = EitherE Int :+: ChoiceE :+: VoidE}
 {e = L}
 {l = T L R}
 {al = Algebra.Either @{Algebra.Concat}}

runTooBigCatch' : ?
runTooBigCatch' = runIdentity . runEitherT . runListT $ tooBigCatch [5, 7, 1]
 {sig =  ChoiceE :+: EitherE Int :+: VoidE}
 {l = L}
 {e = T L R}
 {al = Algebra.Concat @{Algebra.Either}}

-----------------------

||| Generate squares up to n.
||| For every pair of squares, write its sum
||| to the context only if the sum is odd.
||| We test the system by performing the writes all the time
||| inside a `try` block. But if a sum is even we fail inside that block.
||| The system handles backtracking of state for us.
||| We also print intermediate results to console.
exceptionStateListPrint :
     (l : Inj ChoiceE sig)
  => (r : Inj (ReaderE Int) sig)
  => (w : Inj (WriterE (List Int)) sig)
  => (e : Inj (EitherE String) sig)
  => (io : Inj (LiftE IO) sig)
  => (al : Algebra sig m)
  => m ()
exceptionStateListPrint = do
  n <- ask {r = Int}
  let gen = oneOf (takeBefore (> n) $ map (\x => x * x) [2..])
  x <- gen
  y <- gen
  try {e = String}
    (do tell {w = List Int} [x + y]
        if (x + y) `mod` 2 == 0
           then
             fail {sig} {e = String} "even"
           else do
             lift {n = IO} (putStrLn "odd: \{show x} + \{show y} = \{show (x + y)}"))
    (\_ => pure ())


runExceptionStateListPrint : IO ()
runExceptionStateListPrint = do
  res <- runEitherT . runWriterT . runListT . runReaderT 50 $ exceptionStateListPrint
   {sig = ReaderE Int :+: ChoiceE :+: WriterE (List Int) :+: EitherE String :+: Lift IO}
   {r = L}
   {l = T L R}
   {w = T (T L R) R}
   {e = T (T (T L R) R) R}
   {io = T (T (T R R) R) R}
   {al = Algebra.Reader
          @{Algebra.Concat
            @{Algebra.ConcatLeft
              @{%search}
              @{Algebra.Either}}}}
  printLn (map snd res)

-----------------------

pythag : (l : Inj ChoiceE sig)
      => (al : Algebra sig m)
      => (alt : Alternative m)
      => m (Int, Int, Int)
pythag = do
  a <- oneOf [1..10]
  b <- oneOf [1..10]
  c <- oneOf [1..10]
  guard (a * a + b * b == c * c)
  pure (a, b, c)

runPythag : ?
runPythag = runIdentity . runListT $ pythag
  {sig = ChoiceE :+: VoidC}
  {l = L}
  {al = Algebra.Concat @{Algebra.Void}}
  {alt = ListT}

-----------------------

main : IO ()
main = pure ()
