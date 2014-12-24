(** * A constructor for simple types *)

Require Import ObAxioms.
Require Import Lambda.
Local Open Scope Ob_scope.

Section A.
  Local Open Scope Lambda_scope.
  Let x := VAR 0.
  Let y := VAR 1.
  Let z := VAR 2.

  (*
  Notation "< x , y >" := ().
  Notation "x --> y" := ((B*y)o(C*B*x)) (at level 55, right associativity).
  *)
  Definition PAIR := encode (\x, \y, \z, z * x * y).

End A.

Definition A := Join (fun sr => sr = PAIR*(sr*K)*(sr*F) /\ (sr*F)o(sr*K) [= I).

Theorem A_is_definable: definable A.
Proof.
  unfold A; unfold Join.
  (* TODO *)
Admitted.

Definition fixes (a : Ob) (x : Ob) := a*x = x.

Definition semi : Ob.
Admitted.

Theorem semi_inhabs:
  forall x, fixes semi x -> x = BOT \/ x = I \/ x = TOP.
Proof.
  (* TODO *)
Admitted.
