(** * A constructor for simple types *)

Require Import ObAxioms.
Require Import Lambda.

Open Scope Lambda_scope.
Open Scope Ob_scope.

Section is_pair.
  Let z := VAR 0.
  Let pair (x y : Ob) := encode (\z, z * [x] * [y])%Lambda.
  Definition is_pair (x : Ob) := x = pair (x * K) (x * F).
End is_pair.

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
