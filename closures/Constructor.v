(** * A constructor for simple types *)

Require Import ObAxioms.
Require Import Lambda.

Open Scope Lambda_scope.
Open Scope Ob_scope.

Section PAIR.
  Let z := VAR 0.

  Definition PAIR (x y : Ob) := encode (\z, z * [x] * [y])%Lambda.
  Definition is_pair (x : Ob) := x = PAIR (x * K) (x * F).
End PAIR.

Definition A := Join (fun sr => is_pair sr /\ (sr*F)o(sr*K) [= I).
Notation "\\ x , y ; z" := ([A] * \x, \y, z)%Lambda
  (at level 59, right associativity) : Lambda_scope.

Section A_example.
  Let a := VAR 0.
  Let a' := VAR 1.
  Example A_example := (\\a,a'; a --> a').
End A_example.

Theorem A_is_definable: definable A.
Proof.
  unfold A; unfold Join.
  (* TODO: use the Bohm-out technique *)
Admitted.
