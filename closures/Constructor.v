(** * A constructor for simple types *)

Require Import ObAxioms.
Require Import ObTactics.
Require Import Lambda.

Open Scope Lambda_scope.
Open Scope Ob_scope.

Section is_pair.
  Let x := VAR 0.
  Let y := VAR 1.
  Let z := VAR 2.
  Definition pair := encode (\x,\y,\z, z * x * y).
  Definition is_pair (x : Ob) := x = pair * (x * K) * (x * F).
End is_pair.
Notation "<< x , y >>" := (pair * x * y)%Ob : Ob_scope.
Notation "<< x , y >>" := ([pair] * x * y)%Lambda : Lambda_scope.

Lemma pair_is_pair : forall x y, is_pair << x, y>>.
Proof.
  intros x y. compute. reduce 100; auto.
Qed.

Definition A_prop (sr : Ob) := is_pair sr /\ (sr*F)o(sr*K) [= I.
Definition A := Join A_prop.
Notation "\\ x , y ; z" := ([A] * \x, \y, z)%Lambda
  (at level 59, right associativity) : Lambda_scope.

Section A_example.
  Let a := VAR 0.
  Let a' := VAR 1.
  Let A_example := (\\a,a'; a --> a').
End A_example.

Section raise.
  Let x := VAR 3.
  Let y := VAR 4.

  Definition raise := encode (\x, \y, x).
  Definition lower := encode (\x, x * [TOP]).

  Definition pull := encode (\x, \y, x || [div] * y).
  Definition push := encode (\x, x * [BOT]).
End raise.

Ltac A_prop_pair :=
  unfold A_prop; split; [apply pair_is_pair | reduce 100; auto].

Lemma A_I_I : A_prop <<I, I>>.
Proof. A_prop_pair. Qed.

Lemma A_raise_lower : A_prop <<raise, lower>>.
Proof. A_prop_pair. Qed.

Lemma A_pull_push : A_prop <<pull, push>>.
Proof. A_prop_pair. Qed.

Section compose.
  Let s := VAR 0.
  Let a := VAR 1.
  Let a' := VAR 2.
  Let b := VAR 3.
  Let b' := VAR 4.

  Definition compose := encode
    (\s, s*\a,\a', s*\b,\b', <<a*b, b'*a'>>).

  Definition conjugate := encode
    (\s, s*\a,\a', s*\b,\b', <<(a'-->b), (a-->b')>>).
End compose.

Lemma A_compose: forall a, A_prop a -> A_prop (conjugate * a).
Proof.
  intros a H.
  unfold A_prop.
  (* TODO *)
Admitted.

Definition A_prefix :=
  (  K * <<I, I>>
  || K * <<raise, lower>>
  || K * <<pull, push>>
  || compose
  || conjugate
  ).
Definition A_def := Y * A_prefix.

Lemma A_sound: A_def [= A.
Proof.
  unfold A_def.
  apply Y_lfp.
  intros y.
  (* TODO *)
Admitted.

Lemma A_complete: A [= A_def.
Proof.
  unfold A_def.
  apply LESS_conv.
  intros f Hdef Hconv.
  induction Hconv.
  induction Hdef.
  (* TODO *)
Admitted.

Theorem A_definable: A = A_def.
Proof.
  apply LESS_antisym ; apply A_sound || apply A_complete.
Qed.
