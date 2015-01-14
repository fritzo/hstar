(** * A constructor for simple types *)

Require Export Codes.
Open Scope code_scope.

Section exp.
  Context {Var : Set}.
  Let a := make_var Var 0.
  Let b := make_var Var 1.
  Let f := make_var Var 2.
  Definition exp := Eval compute in close (\a, \b, \f, b o f o a).
End exp.
Notation "x --> y" := (exp * x * y)%code : code_scope.

Lemma exp_i_i (Var : Set) : I --> I == (I : Code Var).
Proof.
  unfold exp; beta_eta.
Qed.

Section pair.
  Context {Var : Set}.
  Let x := make_var Var 0.
  Let y := make_var Var 1.
  Let f := make_var Var 2.
  Definition pair := Eval compute in close (\x,\y,\f, f * x * y).
End pair.
Notation "<< x , y >>" := (pair * x * y)%code : code_scope.

Definition is_pair {Var : Set} (x : Code Var) := x == <<x * K, x * (K * I)>>.
Lemma pair_is_pair (Var : Set) (x y : Code Var) : is_pair <<x, y>>.
Proof.
  hnf; unfold pair; beta_reduce; auto.
Qed.

Definition sub_pair {Var : Set} (x : Code Var) := x [= <<TOP, TOP>>.
Lemma sub_pair_pair (Var : Set) (x y : Code Var) : sub_pair <<x, y>>.
Proof.
  unfold sub_pair; unfold pair; eta_expand as f; beta_reduce.
  monotonicity; auto.
Qed.

Definition sub_pair_elim_intro {Var : Set} (x : Code Var) :
  sub_pair x -> x [= <<x*K, x*(K*I)>>.
Proof.
  unfold sub_pair; unfold pair; simpl.
  intros H. (* eta_expand in H. FIXME eta_expand is borken *)
  eta_expand as f; beta_reduce.
Admitted.

Section raise.
  Context {Var : Set}.
  Let x := make_var Var 3.
  Let y := make_var Var 4.

  Definition raise := Eval compute in close (\x, \y, x).
  Definition lower := Eval compute in close (\x, x * TOP).

  Definition pull := Eval compute in close (\x, \y, x || code_div * y).
  Definition push := Eval compute in close (\x, x * BOT).
End raise.

Section compose.
  Context {Var : Set}.
  Let s := make_var Var 0.
  Let a := make_var Var 1.
  Let a' := make_var Var 2.
  Let b := make_var Var 3.
  Let b' := make_var Var 4.

  Definition compose := Eval compute in close
    (\s, s*\a,\a', s*\b,\b', <<a o b, b' o a'>>).

  Definition conjugate := Eval compute in close
    (\s, s*\a,\a', s*\b,\b', <<a' --> b, a --> b'>>).
End compose.

Definition A {Var : Set} : Code Var :=
  Eval compute in
  Y * ( K * <<I, I>>
     || K * <<raise, lower>>
     || K * <<pull, push>>
     || compose
     || conjugate).

Notation "\\ x , y ; z" := (A * \x, \y, z)%code : code_scope.

Section A_example.
  Variable Var : Set.
  Let a := make_var Var 0.
  Let a' := make_var Var 1.
  Let A_example : Code Var := close (\\a,a'; a --> a').
End A_example.

Lemma A_sound (Var : Set) (r s : Code Var) : <<s, r>> [= A -> r o s [= I.
Proof.
  unfold A.
  (*
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

(** ** A strong characterization of [A] *)

Lemma A_pair (Var : Set) : (A : Code Var) [= <<TOP, TOP>>.
Proof.
  (* TODO *)
Admitted.

Lemma A_I_I (Var : Set) : <<I, I>> [= (A : Code Var).
Proof.
  unfold A.
  assert (I o I [= (I : Code Var)) as Heq.
    eta_expand as x; beta_simpl; reflexivity.
  (* TODO adapt the beta_eta tactic from Points to Codes:
  TODO
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

Lemma A_compose : forall a, A_prop a -> A_prop (compose * a).
Proof.
  intros a H.
  unfold A_prop in H; destruct H as [Hpair Hless].
  unfold is_pair in Hpair.
  rewrite Hpair.
  unfold A_prop; split.
    compute; beta_reduce; auto.
  compute; eta_expand; beta_reduce.
  transitivity (a * (K*I) * (a * K * H));
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
  transitivity (a * (K*I) * (a * K * (H * H0)));
    monotonicity; eta_expand in Hless; apply Hless.
Qed.
*)

Lemma A_complete (Var : Set) (s r : Code Var) : r o s [= I -> <<s, r>> [= A.
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

Theorem A_implicit (Var : Set) (x f : Code Var) :
  x [= A * f <-> (forall s r : Code Var, r o s [= I -> x [= f * s * r).
Proof.
  (* TODO *)
Admitted.
