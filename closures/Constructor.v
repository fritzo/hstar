(** * A constructor for simple types *)

Require Import ObAxioms.
Require Import Lambda.
Local Open Scope Ob_scope.

Section pair.
  Local Open Scope Lambda_scope.
  Let x := VAR 0.
  Let y := VAR 1.
  Let z := VAR 2.

  Definition pair := encode (\x, \y, \z, z * x * y).
End pair.

Definition A := Join (fun sr => sr = pair*(sr*K)*(sr*F) /\ (sr*F)o(sr*K) [= I).
Open Scope Lambda_scope.
  Notation "\\ x , y ; z" := ([A] * \x, \y, z)
    (at level 59, right associativity) : Lambda_scope.

  Let a := VAR 0.
  Let a' := VAR 1.
  Example A_example := (\\a,a'; a --> a').
Close Scope Lambda_scope.

Theorem A_is_definable: definable A.
Proof.
  unfold A; unfold Join.
  (* TODO: use the Bohm-out technique *)
Admitted.
