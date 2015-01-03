[![Build Status](https://travis-ci.org/fritzo/hstar.svg?branch=master)](https://travis-ci.org/fritzo/hstar)

# Inadvertently typed &lambda;-join-calculus

This project attempts to formally reason in Coq about
two untyped &lambda;-calculi that act like typed &lambda;-calculi.

## Introduction

In the mid 1970's Dana Scott <a href="#user-content-1">[1]</a>
developed an idiom of embedding types as closure operators
(nondecreasing idempotent functions)
in lattice models of &lambda;-calculus.
His original work showed that this types-as-closures idiom
leads to a rich type structure in D<sub>&infin;</sub> models,
although the type system is inconsistent under the Curry-Howard correspondence
due to the presence of a top element that inhabits every type.
More recently, <a href="#user-content-2">[2]</a> showed that many of the atomic
datatypes are definable with only &lambda;-calculus and a binary join operator,
after a suitable extensional collapse by
Hyland and Wadsworth's axiom H<sup>&ast;</sup>

    H* |- M = N   iff   forall C[ ], C[M] converges <--> C[N] converges

This Coq development attempts to formalize the proof in
<a href="#user-content-2">[2]</a>
and extend the result to probabilistic programming languages.
We reason in a language of ordered combinatory algebras,
treating the Scott ordering `[=` as the basic relation.

Our main result is to develop type systems within two untyped universes
and obtain algebraic types such as `a -> b := \f. b o f o a`
and case analysis theorems such as for the `bool` lattice, for example:

    I [= a   a = a o a            a : type   a x = x
    ------------------ closures   ------------------ fixedpoints
        a : type                         x : a

    a : type   b : type    a : type   b : type
    -------------------    -------------------    -----------    ----------
       a -> b : type          a x b : type        bool : type    nat : type

                 x : bool
    ------------------------------------ bool induction principle
    x = K    x = F    x = BOT    x = TOP

The type system supports algebraic, dependent, polymorphic, and intersection
types, as well as atomic types and a type of all types.

The reasoning principles developed here are intended to be used in the
[Pomagma](http://github.com/fritzo/pomagma)
forward-chaining inference engine.

- [1] <a name="1"/>
  Dana Scott (1976)
  ["Datatypes as Lattices"](http://www.cs.ox.ac.uk/files/3287/PRG05.pdf)
- [2] <a name="2"/>
  Fritz Obermeyer (2009)
  [Automated Equational Reasoning in Nondeterministic &lambda;-Calculi Modulo Theories H&ast;](http://fritzo.org/thesis.pdf)

## Organization

* [/src](/src) - Working draft of Coq development
* [/sandbox](/sandbox) - Sketches in Coq and Isabelle

## License

Copyright (c) 2014-2015 Fritz Obermeyer.<br/>
All code is released under the
[Apache 2.0 License](http://www.apache.org/licenses/LICENSE-2.0).
