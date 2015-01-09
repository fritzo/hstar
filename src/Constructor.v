(** * A constructor for simple types *)

Require Export Points.
(*
Require Import BohmTrees.
*)

Section Exp.
  Open Scope code_scope.
  Variable Var : Set.
  Let a := make_var Var 0.
  Let b := make_var Var 1.
  Let f := make_var Var 2.
  Definition Exp := Eval compute in close (\a, \b, \f, b o f o a).
End Exp.
Notation "x --> y" := (Exp _ * x * y)%code : code_scope.
Notation "x --> y" := ([Exp _] * x * y)%point : point_scope.

Lemma exp_i_i (Var : Set) : I --> I = (I : Point Var).
Proof.
  unfold Exp; beta_eta.
Qed.

Section Pair.
  Open Scope code_scope.
  Variable Var : Set.
  Let x := make_var Var 0.
  Let y := make_var Var 1.
  Let f := make_var Var 2.
  Definition Pair := Eval compute in close (\x,\y,\f, f * x * y).
End Pair.
Notation "<< x , y >>" := (Pair _ * x * y)%code : code_scope.
Notation "<< x , y >>" := ([Pair _] * x * y)%point : point_scope.

Definition is_pair {Var : Set} (x : Point Var) := x = <<x * K, x * (K * I)>>.
Lemma pair_is_pair (Var : Set) (x y : Point Var) : is_pair <<x, y>>.
Proof.
  hnf; unfold Pair; beta_reduce; auto.
Qed.

Definition sub_pair {Var : Set} (x : Point Var) := x [= <<TOP, TOP>>.
Lemma sub_pair_pair (Var : Set) (x y : Point Var) : sub_pair <<x, y>>.
Proof.
  unfold sub_pair; unfold Pair; eta_expand as f; beta_reduce.
  monotonicity; auto.
Qed.

Definition sub_pair_elim_intro {Var : Set} (x : Point Var) :
  sub_pair x -> x [= <<x*K, x*(K*I)>>.
Proof.
  unfold sub_pair; unfold Pair; simpl.
  intros H; eta_expand in H.
  eta_expand as f; beta_reduce.
  (* TODO *)
Admitted.

Definition A {Var : Set} :=
  point_sup (<<s, r>> for s : Point Var for r : Point Var if r o s [= I).
Notation "\\ x , y ; z" := (A * \x, \y, z)%code : code_scope.
Notation "\\ x , y ; z" := (A * \x, \y, z)%point : point_scope.

Section A_example.
  Variable Var : Set.
  Let a := [make_var Var 0].
  Let a' := [make_var Var 1].
  Let A_example : Point Var := point_close (\\a,a'; a --> a').
End A_example.

Section raise.
  Variable Var : Set.
  Let x := [make_var Var 3].
  Let y := [make_var Var 4].

  Definition raise := point_close (\x, \y, x).
  Definition lower := point_close (\x, x * TOP).

  Definition pull := point_close (\x, \y, x || [code_div] * y).
  Definition push := point_close (\x, x * BOT).
End raise.

Lemma A_I_I (Var : Set) : <<I, I>> [= (A : Point Var).
Proof.
  unfold A.
  assert (I o I [= (I : Point Var)) as Heq; eta_expand; beta_reduce; auto.
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
  Variable Var : Set.
  Let s := [make_var Var 0].
  Let a := [make_var Var 1].
  Let a' := [make_var Var 2].
  Let b := [make_var Var 3].
  Let b' := [make_var Var 4].

  Definition compose := point_close
    (\s, s*\a,\a', s*\b,\b', <<a o b, b' o a'>>).

  Definition conjugate := point_close
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
  apply LESS_trans with (a * (K*I) * (a * K * H));
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
  apply LESS_trans with (a * (K*I) * (a * K * (H * H0)));
    monotonicity; eta_expand in Hless; apply Hless.
Qed.
*)

Definition A_def {Var : Set} : Point Var :=
  Y * ( K * <<I, I>>
     || K * <<raise _, lower _>>
     || K * <<pull _, push _>>
     || compose _
     || conjugate _).

Lemma A_sound (Var : Set) : A_def [= (A : Point Var).
Proof.
  (*
  unfold A.
  apply Join_lub.
  *)
  (* unfold A_prop; split. *)
  (*
  unfold A_def.
  apply Y_lfp.
  intros y Hless.
  repeat (rewrite J_beta || rewrite K_beta).
  repeat apply J_lub.
  *)
  (* TODO *)
Admitted.

Lemma A_complete (Var : Set) : (A : Point Var) [= A_def.
Proof.
  unfold A.
  (*
  apply Join_lub; unfold is_upper_bound.
  intros sr; induction sr as [[s r] Hless].
  apply LESS_conv.
  intros c Hdef Hconv.
  inversion Hconv.
  *)
  (* TODO *)
Admitted.

Theorem A_definable (Var : Set) : (A : Point Var) = A_def.
Proof.
  apply point_le_antisym ; apply A_sound || apply A_complete.
Qed.
