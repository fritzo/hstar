(** * Reasoning about least fixed points *)

Require Import Coq.Program.Basics.
Require Import Coq.Setoids.Setoid.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Export Combinators.
Open Scope code_scope.

Fixpoint power {Var : Set} (f : Code Var) (n : nat) : Code Var :=
  match n with
  | 0 => I
  | Succ n' => f o (power f n')
  end.

Notation "f ^ n" := (power f n) : code_scope.

Lemma power_0 (Var : Set) (f x : Code Var) : f ^ 0 * x == x.
Proof. simpl; beta_simpl; auto. Qed.

Lemma power_1 (Var : Set) (f x : Code Var) : f ^ 1 * x == f * x.
Proof. simpl; beta_simpl; auto. Qed.

Lemma power_2 (Var : Set) (f x : Code Var) : f ^ 2 * x == f * (f * x).
Proof. simpl; beta_simpl; auto. Qed.

Definition code_le_limit {Var : Set} (x : Code Var) (f : nat -> Code Var) :=
  forall n, f n [= x.

Definition code_eq_limit {Var : Set} (x : Code Var) (f : nat -> Code Var) :=
  code_le_limit x f /\ forall y, code_le_limit y f -> x [= y.

Lemma Y_limit_ub (Var : Set) (f : Code Var) (n : nat) : f ^ n * BOT [= Y * f.
Proof.
  induction n.
    simpl; beta_simpl; auto.
  unfold power; fold (@power Var); rewrite beta_b.
  rewrite beta_y; monotonicity.
Qed.

Lemma Y_limit_lb
  (Var : Set) (f : Code Var)
  (Var' : Set) (c : Code Var') (b : Var -> Code Var') :
  conv (c * (Y * f @ b)) -> exists n, conv (c * (f ^ n * BOT @ b)).
Proof.
  (* sketch: prove the only beta path from [Y * f] to [f ...] is [beta_y]. *)
Admitted.

Lemma Y_limit_lub (Var : Set) (f x : Code Var) :
  (forall n : nat, f ^ n * BOT [= x) -> Y * f [= x.
Proof.
  unfold code_le; intros Hl Var' c b Hc.
  apply Y_limit_lb in Hc as [n Hn]; eauto.
Qed.

Lemma Y1_as_limit (Var : Set) (f : Code Var) :
  code_eq_limit (Y * f) (fun n => f ^ n * BOT).
Proof.
  split; unfold code_le_limit.
    apply Y_limit_ub.
  apply Y_limit_lub.
Qed.

Lemma Y_lfp (Var : Set) (f x : Code Var) : f * x [= x -> Y * f [= x.
Proof.
  intro Hl.
  assert (forall n : nat, f ^ n * BOT [= x).
    induction n.
      simpl; beta_simpl; auto.
    unfold power; fold (@power Var); rewrite beta_b.
    rewrite <- Hl; monotonicity.
  apply Y_limit_lub; auto.
Qed.

Lemma Y1_idem (Var : Set) (f : Code Var) : Y * (f o f) = Y * f.
Proof.
Admitted.

Lemma Y_S_right (Var : Set) (f g : Code Var) :
  Y * (S * f * g) = Y * (C * f * (Y * (S * f * g))).
Admitted.

Lemma Y_S_left (Var : Set) (f g : Code Var) :
  Y * (S * f * g) = Y * (B * (Y * (S * f * g)) * g).
Admitted.

Lemma Y_ub (Var : Set) (f b : Code Var) :
  (forall x, x [= b -> f * x [= b) -> Y * f [= b.
Proof.
Admitted.

Lemma Y_ident (Var : Set) (y : Code Var) : y == S * I * y -> y = Y.
Proof.
Admitted.

Lemma V_as_limit (Var : Set) (f : Code Var):
  code_eq_limit (V * f) (fun n => f ^ n).
Proof.
  split; unfold code_le_limit.
    induction n; simpl.
      rewrite beta_v; rewrite pi_j_left; auto.
    rewrite beta_v; rewrite pi_j_right.
    rewrite IHn; auto.
  intros y Hy.
Admitted.

Lemma V1_as_limit (Var : Set) (f x : Code Var):
  code_eq_limit (V * f * x) (fun n => f ^ n * x).
Proof.
  split; unfold code_le_limit.
    induction n; simpl.
      rewrite beta_v; rewrite pi_j_left; auto.
    rewrite beta_v; rewrite pi_j_right.
    beta_simpl; monotonicity.
  intros y Hy.
Admitted.
