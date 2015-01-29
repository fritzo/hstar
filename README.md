[![Build Status](https://travis-ci.org/fritzo/hstar.svg?branch=master)](https://travis-ci.org/fritzo/hstar)
![Proof Status](https://img.shields.io/badge/proofs-68_holes-red.svg?style=flat)

Holes | File
-----:|:------------------------------------------------------------
   14 | [Types](src/Types.v)
   13 | [InformationOrdering](src/InformationOrdering.v)
   12 | [Nontermination](src/Nontermination.v)
   10 | [Codes](src/Codes.v)
    8 | [LeastFixedPoint](src/LeastFixedPoint.v)
    8 | [TypeConstructor](src/TypeConstructor.v)
    3 | [Combinators](src/Combinators.v)

# Inadvertently typed &lambda;-join-calculus

This project attempts to formally reason in Coq about
two untyped &lambda;-calculi that act like typed &lambda;-calculi.

## Introduction

In the early 1970's Dana Scott <a href="#user-content-1">[1]</a>
developed an idiom of implementing data types as
nondecreasing idempotent functions
in lattice models of untyped &lambda;-calculus.
Scott's original work showed that this types-as-closures idiom
leads to a rich type structure in D<sub>&infin;</sub> and P(&omega;) models,
although the type system is inconsistent under the Curry-Howard correspondence
due to the presence of a top element that inhabits every type.
More recently, <a href="#user-content-2">[2]</a> showed that many of the atomic
datatypes are definable with only &lambda;-calculus and a binary join operator,
after a suitable extensional collapse by
Hyland and Wadsworth's axiom H&#42;:

    M = N   iff   forall context C[ ], C[M] converges <--> C[N] converges

The Coq developments in this project attempt to formalize the construction in
<a href="#user-content-2">[2]</a>
and extend the result to probabilistic programming languages,
similar to Jean Goubault-Larrecq's recent full-abstraction result
<a href="#user-content-3">[3]</a>.
We reason in a language of ordered combinatory algebras,
treating the Scott ordering `[=` as the basic relation.
We develop type systems within two untyped universes
and obtain algebraic types such as `a -> b := \f. b o f o a`.
The type system supports algebraic, dependent, polymorphic, and intersection
types, as well as atomic types and a type of all types; for example

    I [= a    a = a o a            a : type    a x = x
    =================== closures   ================== fixedpoints
          a : type                        x : a

    forall x:a, f x [= g x
    ======================== universal quantification
              f o a [= g o a

    a : type    b : type    a : type    b : type    a : type    b : type
    --------------------    --------------------    --------------------
       a -> b : type            a * b : type            a + b : type

    ---------    -----------    ----------
    TOP : typ    bool : type    nat : type

The main goal is to prove a set of induction principles supporting
case analysis for well typed terms, for example:

                              p TOP [= q TOP
    forall x:a, forall y:b, p (x,y) [= q (x,y)
    ------------------------------------------ product induction principle
                forall xy:a*b, p xy [= q xy

                    p TOP [= q TOP
                    p BOT [= q BOT
    forall x:a, p (inl x) [= q (inl x)
    forall y:b, p (inr y) [= q (inr y)
    ---------------------------------- sum induction principle
      forall xy:a+b, p xy [= q xy

                p TOP [= q TOP
    -------------------------- TOP induction principle
    forall x:TOP, p x [= q x

                 p TOP [= q TOP
                 p BOT [= q BOT
                   p K [= q K    
                   p F [= q F    
    --------------------------- bool induction principle
    forall b:bool, p b [= q b

                       p TOP [= q TOP
                       p BOT [= q BOT
                      p zero [= q zero      
    forall n:nat, p (succ n) [= q (succ n)
    -------------------------------------- nat induction principle
           forall n:nat, p n [= q n

The reasoning principles developed here are intended to be used in the
[Pomagma](http://github.com/fritzo/pomagma)
forward-chaining inference engine.

## References

- [1] <a name="1"/>
  Dana Scott (1976)
  [Datatypes as Lattices](http://www.cs.ox.ac.uk/files/3287/PRG05.pdf)
- [2] <a name="2"/>
  Fritz Obermeyer (2009)
  [Automated Equational Reasoning in Nondeterministic &lambda;-Calculi Modulo Theories H&#42;](http://fritzo.org/thesis.pdf)
- [3] <a name="3"/>
  Jean Goubault-Larrecq (2015)
  [Full abstraction for non-deterministic and probabilistic extensions of PCF I: The angelic cases]
  (http://www.lsv.ens-cachan.fr/Publis/PAPERS/PDF/jgl-jlap14.pdf)

## License

Copyright (c) 2014-2015 Fritz Obermeyer.<br/>
All code is released under the
[Apache 2.0 License](http://www.apache.org/licenses/LICENSE-2.0).
