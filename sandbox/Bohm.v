(** * Bohm's theorem for SKJ *)

(** Bohm's theorem for lambda-calculus shows separability :
    for every pairs of distinct normal forms [x,y],
    there is a context in which they reduce to [K,F].
    SKJ lacks a normal form predicate,
    so we use instead the convergence predicate [conv],
    or equivalently [red (div * x) TOP] for an identified [TOP] term.
    *)

Require Import ObAxioms.
Require Import Lambda.

Open Scope Ob_scope.

(* FIXME this is still not quite right *)
Theorem Bohms_theorem :
  forall i b c, i [= I -> conv (c * i) ->
  {c' : Ob & conv (c' * i) & conv (c * b) -> conv (c' * b)}.
Proof.
  (* TODO *)
Admitted.
