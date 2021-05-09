### The goal of this document:
Show how to implement a parser of char tokens via a combination of effects.

#### What does a parser do?
A parser is just a program that takes some input structure, usually quite loose in its specification, and tries to shape it into a more structured representation. A typical example of such programs is a string-to-json conversions. Another one is parsing of text into a high-level language syntax tree.

#### What features does a typical parser have?
- Parsers work with a collection of tokens, `Char`s in our case, examining
  the tokens one by one and possibly consuming them sequentially, thus making progress.

- Parsers may throw errors when the input doesn't match the specification.

- Parses may explore multiple alternative ways of reading and interpreting the input.

Those three attributes form a minimal set of what is needed to write a parser.

Every attribute from the set can be thought of as an extra "power", or in other words - effect, that a computation can summon or apply compared to its effectless counterpart.

Hence, the three effects above are:
  1) reading/writing from/to the context (i.e. state)
  2) throwing errors, terminating further computation, and possibly recovering from them (i.e. exceptions)
  3) Non-deterministic branching, where the condition for picking one path
      over the other (or keeping both) is not specified until the program is run (i.e. non-determinism)

#### Composing effects - the disjoint union.

Now that we know what kind of superpowers our computation shall have, let's think how we can compose those effects into one structure.

When we want to apply one of the effects in our program, we explicitly say which one we want at the given instant of time. And it doesn't make sense to dispatch multiple ones simultaneously (e.g. you can't unite `read` and `fail` in one atomic action).

All of that means we can encode any effect from the chosen set as a disjoint union (alternative names are `sum type` and the familiar `Either`). Three or more effects can be represented as nested `Either`s.

As we'll see later, in the library we call that structure `:+:`. We can't go with the built-in `Either`
because there is still a difference between the two.

#### The library

In the library we call a composition of effects an `effect signature`.
Most of the time we want a computation that is written in terms of an effect signature `X`
 to be callable from a computation with signature `Y`, if `X` can be embedded into `Y`.
For example, if a function is known to potentially throw, having no other effects, we want it to be accessible from a function with a richer set of effects, failure being one of them.

To account for this, instead of writing concrete signatures we keep their value polymorphic, while extending the list of arguments of our computation with an interface constraint for each effect we want in the signature:
```idris
Inj (StateE Int) sig
Inj (FailE String) sig
```
In the above snippet, we specify two effects to be a part of the signature, that might contain other effects we don't care about.

`Inj` is a very simple concept: in the first line it says that the `Int` state is one of the effects of the signature `sig`. The second line says the same about failures carrying `String` error messages.
`Inj` stands for injection, meaning that we can inject a small thing, one effect, into a larger thing, a union of many effects.

In programs we generally list those `Inj` constraints in a row.

Let's write our first function that acts on the input tokens.
```idris
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
  c :: rest <- ask {sig} {r = List Char}
    | [] => fail {a = Char} "End of input"
  tell {sig} {w = List Char} rest
  pure c
```

Walking through the code line by line:

First we import the modules we are going to need to write a parser.
When working with effects, we always need to import `Control.EffectAlgebra`, that defines effect handling and reexports
other core definitions.

Effects reside in `Control.Effect.*`.

The execution of effects is delegated to monad transformers found in `Control.Monad.*`

The function `nextChar` describes what effects it depends on, via the aforementioned `Inj` constraint.
The last constraint - `Algebra`, carries the information required to interpret the effect signature into a monad `m`.

The body of the function should look very familiar to anyone who has some experience with monads and the `do` notation.
The first line reads the current state from the context, i.e. the list of tokens (`Char`s) to be processed.
Next we pattern match on the result in-place, failing with `"End of input"` if the list of input tokens is empty.
On the next line we "consume" the first available token by writing the tail of the list back to the context.
At the end we return the first token.

Another function that will prove useful later on:
```idris
guardFail : (f : Inj (FailE e) sig)
         => (a : Algebra sig m)
         => Bool
         -> e
         -> m ()
guardFail True  e = pure ()
guardFail False e = fail e
```
We invoke it by sticking in a boolean condition and an instance of the error.
The function silently yields the empty value if the condition is `True` and throws the error on `False`.

Now let's write a function that tries to parse a character based on the supplied predicate:

```idris
parseChar : (e : Inj (FailE String) sig)
         => (r : Inj (StateE (List Char)) sig)
         => (a : Algebra sig m)
         => (Char -> Bool)
         -> String
         -> m Char
parseChar pred err = do
  c <- nextChar
  guardFail {sig} (pred c) err
  pure c
```

Its body is straight forward:
 1. examine the next char (or fail if none is left)
 2. fail if the char doesn't satisfy the predicate
 3. return

Before proceeding, let's define a shortcut for the type of parsers:
```idris
Parser : (sig : (Type -> Type) -> (Type -> Type)) -> (m : Type -> Type) -> Type -> Type
Parser sig m res = (e : Inj (EitherE String) sig)
                => (s : Inj (StateE (List Char)) sig)
                => (n : Inj ChoiceE sig)
                => (a : Algebra sig m)
                => m res
```

`Parser sig m res` reads as: an effectful computation that features exception handling, state and non-determinism, resulting in
a value of type `res`.

`EitherE` is an amped up version of `FailE` that also allows us to catch failures.
`ChoiceE` introduces non-determinism to our programs.

Another useful combinator:
```idris
parseMany : m t -> Parser sig m (List t)
parseMany p = do
  Just x <- try {e = String} {sig} (map Just p) (\_ => pure Nothing)
    | _ => pure []
  map (x ::) (parseMany p)
```
The function takes a computation that results in `t` and produces a computation
that runs the former 0+ times, accumulating the results.
Here we use yet another effectful function `try`, that is a part of `EitherE`:
`try f h` tries to run `f`. If it succeeds, nothing else is run, otherwise it invokes `h` applied to the error value.
In our example we try to run `p`, wrapping its result in `Just`. In case of an error we yield `Nothing`.
Lastly, we recursively try running `p` again, accumulating the freshly returned value, or terminate if `p` can't be applied anymore.

Here is a simple program that hinges on the previous material.

```idris
||| Parses many A's.
testParser1 : Parser sig m (List Char)
testParser1 = parseMany (parseChar (== 'A') "Not A")
```

Let's run it!

Execution of effects works by peeling off the layers, one by one, transforming the computation into a monad transformer stack. It's okay if you are not familiar with them. In our library they serve the sole purpose of intermediary structure between effects and pure programs.

```idris
runParser1 : String -> List (Either String (List Char, List Char))
runParser1 str = runIdentity . runListT . runEitherT . runStateT (unpack str) $ testParser1
  {sig = StateE (List Char) :+: EitherE String :+: ChoiceE :+: VoidE}
  {s = L}
  {e = T L R}
  {n = T (T L R) R}
  {a = Algebra.State @{Algebra.Either @{Algebra.Concat}}}

```

Unfortunately, some of the details (all arguments in braces), that should've been inferred by Idris,
in reality have to be filled in manually by the programmer. Hopefully, eventually we'll be able to alleviate the problem or eliminate it completely.
For the sake of learning, writing out those arguments can be valuable, though.
The `sig` argument is exactly the full effect signature we talked about in the beginning.
`:+:` is almost the same as `Either`, the only difference being the types of its operands.
`:+:` is right associative!
Also notice that at the end of the signature we insert `VoidE`, that can be thought of as an empty effect.
Next three arguments `s` `e` `n` specify how to inject the corresponding single signature into the disjoint union.
`s` is the easiest one - it says that `StateE (List Char)` is located right to the `L`eft of the union.
`e` expresses the fact that `EitherE String` is inside the subpart on the `R`ight of the full union, while with respect to that subpart it is on the `L`eft of it.
`n` - Inside the right subpart of the full union, then again inside the right subpart of the subpart and then on the left.
`T` stands for transitive.
The last argument in braces specifies how to interpret the effect signature. In general, there are multiple ways of interpreting the same effect.
For example, in case of the `WriterE` effect, successive writes can either overwrite the preceding ones or be accumulated all together.
In addition, the target monad, we interpret the effect into, can also vary.
At the moment, all effects are evaluated into monad transformer stacks.
But we are not by any means limited to this choice.

The transformer stack above is evaluated by the composition:
```idris
runIdentity . runListT . runEitherT . runStateT string1
```
Notice the reverse ordering of the `runX` evaluators (compared to the effect signature).

Now you can compute the result of `runParser1 X` from the REPL.

Next useful combinator:
```idris
parseAll : List (m t) -> Parser sig m (List t)
parseAll [] = pure []
parseAll (x :: xs) = map (::) x <*> parseAll xs
```
It takes a list of parsers and succeeds only if every parser from the list succeeds.
The results are grouped back into a list.

```idris
parseString : String -> Parser sig m (List Char)
parseString x =
  parseAll (map (\x => parseChar {sig} (x ==) "Expected \{show x}") (unpack x))
```

A function that makes use of `parseAll` to parse a string.

```idris
testParser2 : Parser sig m (List Char)
testParser2 = parseString "hello"

runParser2 : String -> ?
runParser2 str = runIdentity . runEitherT . runListT . runStateT (unpack str) $ testParser2
  {sig = StateE (List Char) :+: ChoiceE :+: EitherE String :+: VoidE}
  {s = L}
  {n = T L R}
  {e = T (T L R) R}
  {a = Algebra.State @{Algebra.Concat @{Algebra.Either}}}
```

So far so good. Our problems have been kind of "thin", though: there has been only one direction a parser could follow.
What if we want to parse either `A` or `B`?
Here comes non-determinism.

```idris
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
```

The `oneOfM` effectful computation takes a list of computations and threads each constituent through the further program. `oneOfM` has a somewhat opposite meaning of `(<*>)`. The latter chains successive computations. While the former considers every one in parallel.

Last example for today: finding occurrences of the word in the input.

```idris
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
```

Parsers are one of many things that can be modelled via effects.
The great thing about them is universality and composability.
As long as a program's signature states that it supports a subset of effects `X`, among others,
  it can freely and painlessly call any other effectful function of signature `X`.

The full code from the document is available in [`/tests/effect/test002/Parser.idr`](/tests/effect/test002/Parser.idr)
