(** * Reasoning about least fixed points *)

Require Import Coq.Program.Basics.
Require Import Coq.Setoids.Setoid.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Export Combinators.
Open Scope code_scope.

(** ** Suprema of sequences *)

Fixpoint power {Var : Set} (f : Code Var) (n : nat) : Code Var :=
  match n with
  | 0 => I
  | Succ n' => f o (power f n')
  end.

Notation "f ^ n" := (power f n) : code_scope.

Lemma power_0 (Var : Set) (f x : Code Var) : f ^ 0 * x == x.
Proof.
  simpl; beta_simpl; auto.
Qed.

Lemma power_1 (Var : Set) (f x : Code Var) : f ^ 1 * x == f * x.
Proof.
  simpl; beta_simpl; auto.
Qed.

Lemma power_2 (Var : Set) (f x : Code Var) : f ^ 2 * x == f * (f * x).
Proof.
  simpl; beta_simpl; auto.
Qed.

Lemma power_0' (Var : Set) (f : Code Var) : f ^ 0 == I.
Proof.
  beta_eta.
Qed.

Lemma power_1' (Var : Set) (f : Code Var) : f ^ 1 == f.
Proof.
  simpl; beta_eta.
Qed.

Hint Rewrite power_0 power_1 power_0' power_1' : code_simpl.

Lemma power_commute_1 (Var : Set) (f x : Code Var) (n : nat) :
  f * (f^n * x) == f^n * (f * x).
Proof.
  induction n; simpl; code_simpl; auto.
Qed.

Lemma power_commute_1' (Var : Set) (f : Code Var) (n : nat) :
  f o f^n == f^n o f.
Proof.
  induction n; simpl; code_simpl; auto.
Qed.

Lemma power_add (Var : Set) (f x : Code Var) (m n : nat) :
  f^(m + n) * x == f^m * (f^n * x).
Proof.
  induction m; induction n; simpl; code_simpl; auto.
  - replace (m + 0) with m; auto.
  - rewrite IHm; simpl; code_simpl; auto.
Qed.

Lemma power_add' (Var : Set) (f : Code Var) (m n : nat) :
  f^(m + n) == f^m o f^n.
Proof.
  eta_expand as x; beta_simpl; apply power_add.
Qed.

Definition limit_le_code {Var : Set} (f : nat -> Code Var) (x : Code Var) :=
  forall n, f n [= x.

Definition limit_eq_code {Var : Set} (f : nat -> Code Var) (x : Code Var) :=
  limit_le_code f x /\ forall y, limit_le_code f y -> x [= y.

(** ** Applications of limits *)

Lemma Y_limit_ub (Var : Set) (f : Code Var) (n : nat) : f ^ n * BOT [= Y * f.
Proof.
  induction n.
    simpl; beta_simpl; auto.
  unfold power; fold (@power Var); rewrite beta_b.
  rewrite code_eq_y; monotonicity.
Qed.

Lemma Y_limit_lb
  (Var : Set) (f : Code Var)
  (Var' : Set) (c : Code Var') (b : Var -> Code Var') :
  code_conv (c * (Y * f @ b)) -> exists n, code_conv (c * (f ^ n * BOT @ b)).
Proof.
  (* sketch: prove the only beta path from [Y * f] to [f ...] is [code_eq_y]. *)
Admitted.

Lemma Y_limit_lub (Var : Set) (f x : Code Var) :
  (forall n : nat, f ^ n * BOT [= x) -> Y * f [= x.
Proof.
  unfold code_le; intros Hl Var' c b Hc.
  apply Y_limit_lb in Hc as [n Hn]; eauto.
Qed.

Lemma Y1_as_limit (Var : Set) (f : Code Var) :
  limit_eq_code (fun n => f ^ n * BOT) (Y * f).
Proof.
  split; unfold limit_le_code.
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
Proof.
Admitted.

Lemma Y_S_left (Var : Set) (f g : Code Var) :
  Y * (S * f * g) = Y * (B * (Y * (S * f * g)) * g).
Proof.
Admitted.

Lemma Y_ub (Var : Set) (f b : Code Var) :
  (forall x, x [= b -> f * x [= b) -> Y * f [= b.
Proof.
Admitted.

Lemma Y_ident (Var : Set) (y : Code Var) : y == S * I * y -> y = Y.
Proof.
Admitted.

Lemma V_as_limit (Var : Set) (f : Code Var):
  limit_eq_code (fun n => f ^ n) (V * f).
Proof.
  split; unfold limit_le_code.
    induction n; simpl.
      rewrite code_eq_v; rewrite pi_j_left; auto.
    rewrite code_eq_v; rewrite pi_j_right.
    rewrite IHn; auto.
  intros y Hy.
Admitted.

Lemma V1_as_limit (Var : Set) (f x : Code Var):
  limit_eq_code (fun n => f ^ n * x) (V * f * x).
Proof.
  split; unfold limit_le_code.
    induction n; simpl.
      rewrite code_eq_v; rewrite pi_j_left; auto.
    rewrite code_eq_v; rewrite pi_j_right.
    beta_simpl; monotonicity.
  intros y Hy.
Admitted.
