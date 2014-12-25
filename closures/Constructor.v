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

Definition A_prop (sr : Ob) := is_pair sr /\ (sr*F)o(sr*K) [= I.
Definition A := Join A_prop.
Notation "\\ x , y ; z" := ([A] * \x, \y, z)%Lambda
  (at level 59, right associativity) : Lambda_scope.

Section A_example.
  Let a := VAR 0.
  Let a' := VAR 1.
  Example A_example := (\\a,a'; a --> a').
End A_example.

Theorem A_is_definable: definable A.
Proof.
  assert (exists A', A = A' /\ definable A').
  (* TODO Proof sketch
    1. Use Bohm-out technique to carefully construct an A' such that
       for each <s,r>[=A,
         for each context f,
           if f <s,r> converges then f A' converges.
    2. Conclude that A [= A'
    3. Inspect A' to show that also A' [= A.
    4. apply LESS_antisym
    5. Inspect A' to show that A' is definable.
  *)
Admitted.
