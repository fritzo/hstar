(** * A constructor for simple types *)

Require Import ObAxioms.
Require Import Lambda.

Open Scope Lambda_scope.
Open Scope Ob_scope.

Section pair.
  Let x := VAR 0.
  Let y := VAR 1.
  Let z := VAR 2.
  Definition pair := encode (\x,\y,\z, z * x * y).
End pair.
Notation "<< x , y >>" := (pair * x * y)%Ob : Ob_scope.
Notation "<< x , y >>" := ([pair] * x * y)%Lambda : Lambda_scope.

Definition is_pair (x : Ob) := x = <<x * K, x * F>>.
Lemma pair_is_pair : forall x y, is_pair <<x, y>>.
Proof.
  intros x y. compute. beta_reduce; auto.
Qed.

Definition sub_pair (x : Ob) := x [= <<TOP, TOP>>.
Lemma sub_pair_pair : forall x y, sub_pair <<x, y>>.
Proof.
  intros x y. compute. beta_reduce.
  apply LESS_trans with (C*(C*I*TOP)*y);
  monotonicity; auto.
Qed.

Definition sub_pair_elim_intro : forall x, sub_pair x -> x [= <<x*K, x*F>>.
Proof.
  unfold sub_pair, pair; compute.
  intros x H.
  eta_expand as y. beta_reduce.
  eta_expand in H.
  (* TODO *)
Admitted.

Definition A := Join (<<s, r>> for s : Ob for r : Ob if r o s [= I).
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

Lemma A_I_I : <<I, I>> [= A.
Proof.
  unfold A.
  assert (I o I [= I) as Heq; eta_expand; beta_reduce; auto.
  (* TODO
  apply Join_ub_eq with (i := restrict2_intro _ I I Heq).
  *)
Admitted.

(*
Lemma A_raise_lower : A_prop <<raise, lower>>.
Proof.
  unfold A_prop; split;
  [ apply pair_is_pair
  | compute; eta_expand; beta_reduce; auto].
Qed.

Lemma A_pull_push : A_prop <<pull, push>>.
Proof.
  unfold A_prop; split.
  apply pair_is_pair.
  unfold pull.
  freeze div in (compute; eta_expand; beta_reduce).
  rewrite div_BOT; auto.
Qed.
*)

Section compose.
  Let s := VAR 0.
  Let a := VAR 1.
  Let a' := VAR 2.
  Let b := VAR 3.
  Let b' := VAR 4.

  Definition compose := encode
    (\s, s*\a,\a', s*\b,\b', <<a o b, b' o a'>>).

  Definition conjugate := encode
    (\s, s*\a,\a', s*\b,\b', <<(a'-->b), (a-->b')>>).
End compose.

(*
Lemma A_compose : forall a, A_prop a -> A_prop (compose * a).
Proof.
  intros a H.
  unfold A_prop in H; destruct H as [Hpair Hless].
  unfold is_pair in Hpair.
  rewrite Hpair.
  unfold A_prop; split.
    compute; beta_reduce; auto.
  compute; eta_expand; beta_reduce.
  apply LESS_trans with (a * F * (a * K * H));
    monotonicity; eta_expand in Hless; apply Hless.
Qed.

Lemma A_conjugate : forall a, A_prop a -> A_prop (conjugate * a).
Proof.
  intros a H.
  unfold A_prop in H; destruct H as [Hpair Hless].
  unfold is_pair in Hpair.
  rewrite Hpair.
  unfold A_prop; split.
    compute; beta_reduce; auto.
  compute; eta_expand; eta_expand; beta_reduce.
  apply LESS_trans with (a * F * (a * K * (H * H0)));
    monotonicity; eta_expand in Hless; apply Hless.
Qed.
*)

Definition A_def :=
  Y * ( K * <<I, I>>
     || K * <<raise, lower>>
     || K * <<pull, push>>
     || compose
     || conjugate).

Lemma A_sound : A_def [= A.
Proof.
  (*
  unfold A.
  apply Join_lub.
  *)
  (* unfold A_prop; split. *)
  unfold A_def.
  apply Y_lfp.
  intros y Hless.
  repeat (rewrite J_beta || rewrite K_beta).
  repeat apply J_lub.
  (* TODO *)
Admitted.

Lemma A_complete : A [= A_def.
Proof.
  unfold A.
  apply Join_lub; unfold is_upper_bound.
  intros sr; induction sr as [[s r] Hless].
  apply LESS_conv.
  intros c Hdef Hconv.
  inversion Hconv.
  (* TODO *)
Admitted.

Theorem A_definable : A = A_def.
Proof.
  apply LESS_antisym ; apply A_sound || apply A_complete.
Qed.
