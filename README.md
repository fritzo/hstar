[![Build Status](https://travis-ci.org/fritzo/hstar.svg?branch=master)](https://travis-ci.org/fritzo/hstar)

# Inadvertently typed &lambda;-join-calculus

This project is an attempt to formally reason about two untyped &lambda;-calculi
that act like typed &lambda;-calculi in that they support Dana Scott's
types-as-closures idiom <a href="#user-content-1">[1]</a>:

    I [= a   a = a o a    a : type   a x = x
    ------------------    ------------------
        a : type                x : a

with definable algebraic datatypes such as `a -> b := \f. b o f o a`

    a : type   b : type    a : type   b : type
    -------------------    -------------------    -----------    ----------
       a -> b : type          a x b : type        bool : type    nat : type

and case analysis theorems such as

                 x : bool
    ------------------------------------
    x = K    x = F    x = BOT    x = TOP

The &lambda;-calculi are two extensions of pure untyped &lambda;-calculus
under Hyland and Wadsworth's observational equivalence axiom H&ast;.

    M = N  iff  forall C[ ], C[M] converges <--> C[N] converges

The extensions are:

1. pure untyped &lambda;-join-calculus modulo H&ast;,
   providing a model of nondeterministic computation; and

2. pure untyped stochastic &lambda;-join-calculus modulo &Hast;,
   providing a model of computation with
   convex sets of probability distributions.

These &lambda;-calculi are described in <a href="#user-content-2">[2]</a>
and <a href="#user-content-3">[3]</a>.

- [1] <a name="1"/>
  Dana Scott (1976)
  ["Datatypes as Lattices"](http://www.cs.ox.ac.uk/files/3287/PRG05.pdf)
- [2] <a name="2"/>
  Fritz Obermeyer (2009)
  [Automated Equational Reasoning in Nondeterministic &lambda;-Calculi Modulo Theories H&ast;](http://fritzo.org/thesis.pdf)
- [3] <a name="3"/>
  [Pomagma](http://github.com/fritzo/pomagma):
  an inference engine for extensional &lambda;-calculus.

## Organization

* [/src](/src) - Working draft of Coq development
* [/sandbox](/sandbox) - Sketches in Coq and Isabelle

## License

Copyright (c) 2014-2015 Fritz Obermeyer.<br/>
All code is released under the
[Apache 2.0 License](http://www.apache.org/licenses/LICENSE-2.0).
