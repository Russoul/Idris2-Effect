# Idris2-Effect
Experimental effects library for Idris 2

Depends on an unmerged patch: https://github.com/idris-lang/Idris2/pull/1386

For an introduction, see [writing a parser via effects](/docs/example-parser.md)

The effect system is based on the following work:
 1. [Extensible Effects](http://okmij.org/ftp/Haskell/extensible/exteff.pdf) by Oleg Kiselyov, Amr Sabry and Cameron Swords
 2. [Freer Monads, More Extensible Effects](http://okmij.org/ftp/Haskell/extensible/more.pdf) by Oleg Kiselyov and Hiromi Ishii
 3. [Effect Handlers in Scope](http://www.cs.ox.ac.uk/people/nicolas.wu/papers/Scope.pdf) by Nicolas Wu, Tom Schrijvers and Ralf Hinze
 4. [Fusion for Free](https://people.cs.kuleuven.be/~tom.schrijvers/Research/papers/mpc2015.pdf) by Nicolas Wu and Tom Schrijvers

A similar effect system in haskell: [fused-effects](https://github.com/fused-effects/fused-effects)
