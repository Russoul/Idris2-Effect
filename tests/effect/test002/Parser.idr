module Parser

import Data.List
import Data.Either

import Control.EffectAlgebra

import Control.Effect.Exception
import Control.Effect.Fail
import Control.Effect.State
import Control.Effect.NonDet

import Control.Monad.Identity
import Control.Monad.State
import Control.Monad.Either
import Control.Monad.List

import Control.Cont.Void

nextChar : (r : Inj (StateE (List Char)) sig)
        => (f : Inj (FailE String) sig)
        => (a : Algebra sig m)
        => m Char
nextChar = do
  c :: rest <- ask {r = List Char}
    | [] => fail "End of input"
  tell rest
  pure c

guardFail : (f : Inj (FailE e) sig)
         => (a : Algebra sig m)
         => Bool
         -> e
         -> m ()
guardFail True  e = pure ()
guardFail False e = fail e

parseChar : (e : Inj (FailE String) sig)
         => (r : Inj (StateE (List Char)) sig)
         => (a : Algebra sig m)
         => (Char -> Bool)
         -> String
         -> m Char
parseChar pred err = do
  c <- nextChar
  guardFail (pred c) err
  pure c

Parser : (sig : (Type -> Type) -> (Type -> Type)) -> (m : Type -> Type) -> Type -> Type
Parser sig m res = (e : Inj (EitherE String) sig)
                => (s : Inj (StateE (List Char)) sig)
                => (n : Inj ChoiceE sig)
                => (a : Algebra sig m)
                => m res

parseMany : m t -> Parser sig m (List t)
parseMany p = do
  Just x <- try {e = String} (map Just p) (\_ => pure Nothing)
    | _ => pure []
  map (x ::) (parseMany p)

||| Parses many A's.
testParser1 : Parser sig m (List Char)
testParser1 = parseMany (parseChar (== 'A') "Not A")

runParser1 : String -> List (Either String (List Char, List Char))
runParser1 str = runIdentity . runListT . runEitherT . runStateT (unpack str) $ testParser1
  {sig = StateE (List Char) :+: EitherE String :+: ChoiceE :+: VoidE}
  {s = L}
  {e = T L R}
  {n = T (T L R) R}
  {a = Algebra.State @{Algebra.Either @{Algebra.Concat}}}

parseAll : List (m t) -> Parser sig m (List t)
parseAll [] = pure []
parseAll (x :: xs) = map (::) x <*> parseAll xs

parseString : String -> Parser sig m (List Char)
parseString x =
  parseAll (map (\x => parseChar (x ==) "Expected \{show x}") (unpack x))

testParser2 : Parser sig m (List Char)
testParser2 = parseString "hello"

runParser2 : String -> ?
runParser2 str = runIdentity . runEitherT . runListT . runStateT (unpack str) $ testParser2
  {sig = StateE (List Char) :+: ChoiceE :+: EitherE String :+: VoidE}
  {s = L}
  {n = T L R}
  {e = T (T L R) R}
  {a = Algebra.State @{Algebra.Concat @{Algebra.Either}}}

testParser3 : Parser sig m (List Char)
testParser3 =
  oneOfM [parseString "hello", parseString "hi"]

runParser3 : String -> ?
runParser3 str = runIdentity . runListT . runEitherT . runStateT (unpack str) $ testParser3
  {sig = StateE (List Char) :+: EitherE String :+: ChoiceE :+: VoidE}
  {s = L}
  {e = T L R}
  {n = T (T L R) R}
  {a = Algebra.State @{Algebra.Either @{Algebra.Concat}}}

testParser4 : String -> Parser sig m (List Char)
testParser4 str = do
  oneOfM [parseString str, nextChar *> testParser4 str]

runParser4 : String -> String -> List Nat
runParser4 occ str =
             map ((\x => (length str `minus` length x) `minus` length occ) . fst)
           . rights
           . runIdentity
           . runListT
           . runEitherT
           . runStateT (unpack str) $ (testParser4 occ)
  {sig = StateE (List Char) :+: EitherE String :+: ChoiceE :+: VoidE}
  {s = L}
  {e = T L R}
  {n = T (T L R) R}
  {a = Algebra.State @{Algebra.Either @{Algebra.Concat}}}
