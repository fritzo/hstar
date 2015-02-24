(** * A strong characterization of the type constructor [A] *)

Require Import Coq.Logic.Decidable.
Require Import Coq.Program.Basics.
Require Import Coq.Program.Equality.
Require Import Coq.Setoids.Setoid.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Export TypeConstructor.
Require Import Nontermination.
Require Import LeastFixedPoint.
Require Import BohmTrees.
Open Scope code_scope.

(* ------------------------------------------------------------------------ *)
(** ** An implicit definition of [A] *)

Definition is_pair {Var : Set} (x : Code Var) := x == [x * K, x * (K * I)].
Lemma pair_is_pair (Var : Set) (x y : Code Var) : is_pair [x, y].
Proof.
  hnf; unfold pair; beta_reduce; auto.
Qed.

Definition sub_pair {Var : Set} (x : Code Var) := x [= [TOP, TOP].

Instance sub_pair_eq (Var : Set) :
  Proper (code_eq ==> iff) (@sub_pair Var).
Proof.
  unfold sub_pair; intros x x' xx'; split; rewrite xx'; auto.
Qed.

Instance sub_pair_le (Var : Set) :
  Proper (code_le --> impl) (@sub_pair Var).
Proof.
  unfold sub_pair; intros x x' xx' H. rewrite <- xx'; auto.
Qed.

Lemma sub_pair_pair (Var : Set) (x y : Code Var) : sub_pair [x, y].
Proof.
  unfold sub_pair, pair; eta_expand as f; beta_reduce.
  monotonicity; auto.
Qed.

(* FIXME is this true? *)
Lemma sub_pair_elim_intro (Var : Set) (x : Code Var) :
  sub_pair x -> x [= [x*K, x*(K*I)].
Proof.
  unfold sub_pair, pair; simpl.
  intros H. (* eta_expand in H. FIXME eta_expand is borken *)
  eta_expand as f; beta_reduce.
Admitted.

Definition pairish {Var : Set} (x : Code Var) :=
  [BOT, BOT] [= x /\ x [= [TOP, TOP].

(* FIXME is this true? what about for stochastic terms? *)
Lemma pairish_elim (Var : Set) (x f y : Code Var) :
  pairish x ->
  (forall s r, [s, r] [= x -> f * s * r [= y) ->
  x * f [= y.
Proof.
Admitted.

(* should we work only in the lattice inverval [[<BOT,BOT>, <TOP, TOP>]]? *)
Definition A_prop' {Var : Set} (a : Code Var) :=
  [BOT, BOT] [= a /\
  a [= [TOP, TOP] /\
  forall s r, [s, r] [= a -> r o s [= I.

Definition A_prop {Var : Set} (a : Code Var) :=
  sub_pair a /\ forall s r, [s, r] [= a -> r o s [= I.

Instance A_prop_le (Var : Set) : Proper (code_le --> impl) (@A_prop Var).
Proof.
  unfold A_prop; intros x x' xx'; intros [Hs Hl]; split.
     rewrite <- xx'; auto.
  intros s r H; rewrite <- xx' in *; auto.
Qed.

Instance A_prop_eq (Var : Set) : Proper (code_eq ==> iff) (@A_prop Var).
Proof.
  split; destruct H as [Hl Hr]; apply A_prop_le; auto.
Qed.

Ltac A_prop_pair :=
  unfold A_prop; unfold sub_pair; split;
  [ try apply pair_extensionality; auto
  | intros s r H;
    apply pair_extensionality in H;
    destruct H as [Hs Hr];
    rewrite Hs; rewrite Hr
  ].

(* ------------------------------------------------------------------------ *)
(** ** An inductive definition of [A] *)

Lemma A_I_I (Var : Set) : A_prop ([I, I] : Code Var).
Proof.
  A_prop_pair; beta_eta.
Qed.
Hint Resolve A_I_I.

Lemma A_raise_lower (Var : Set) : (@A_prop Var) [raise, lower].
Proof.
  A_prop_pair; eta_expand; beta_simpl; apply lower_raise.
Qed.

Lemma A_pull_push (Var : Set) : (@A_prop Var) [pull, push].
Proof.
  A_prop_pair; eta_expand; beta_simpl; apply push_pull.
Qed.
Hint Resolve A_raise_lower.
Hint Resolve A_pull_push.

Lemma A_compose (Var : Set) (a : Code Var) : A_prop a -> A_prop (compose * a).
Proof.
  unfold A_prop, sub_pair; intros [Hs Ha]; split.
Admitted.
Hint Resolve A_compose.

Lemma A_conjugate (Var : Set) (a : Code Var) :
  A_prop a -> A_prop (conjugate * a).
Proof.
  unfold A_prop, sub_pair; intros [Hs Ha]; split.
Admitted.
Hint Resolve A_conjugate.

(* OLD
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

Inductive A_above {Var : Set} : Code Var -> Prop :=
  | A_above_below x y : x [= y -> A_above y -> A_above x
  | A_above_i_i : A_above [I, I]
  | A_above_raise_lower : A_above [raise, lower]
  | A_above_pull_push : A_above [pull, push]
  | A_above_compose a : A_above a -> A_above (compose * a)
  | A_above_conjugate a : A_above a -> A_above (conjugate * a).
Hint Constructors A_above.

Instance A_above_le (Var : Set) : Proper (code_le --> impl) (@A_above Var).
Proof.
  intros x x' xx' H; apply A_above_below with x; auto.
Qed.

Instance A_above_eq (Var : Set) : Proper (code_eq ==> iff) (@A_above Var).
Proof.
  split; destruct H as [Hl Hr]; apply A_above_le; auto.
Qed.

Lemma A_above_sound (Var : Set) (sr : Code Var) : A_above sr -> A_prop sr.
Proof.
  intro H; induction H; auto.
  rewrite H; auto.
Qed.

(** The main lemma *)

Lemma A_above_complete (Var : Set) (sr : Code Var) : A_prop sr -> A_above sr.
Proof.
  intro H; destruct H as [Hp Hl].
Admitted.

(* ------------------------------------------------------------------------ *)
(** ** A constructive definition of [A] *)

Lemma A_complete (Var : Set) (sr : Code Var) : A_prop sr -> sr [= A.
Proof.
  A_simpl.
  intros H; apply A_above_complete in H.
  induction H; auto.
  - transitivity y; auto.
  - rewrite pi_j_left, pi_j_left, pi_j_left, code_eq_y; beta_simpl; auto.
  - rewrite pi_j_left, pi_j_left, pi_j_right, code_eq_y; beta_simpl; auto.
  - rewrite pi_j_left, pi_j_right, code_eq_y; beta_simpl; auto.
  - rewrite code_eq_y; beta_simpl;
    rewrite pi_j_right, pi_j_left, IHA_above; auto.
  - rewrite code_eq_y; beta_simpl;
    rewrite pi_j_right, pi_j_right, IHA_above; auto.
Qed.

Lemma A_sound (Var : Set) (s r : Code Var) : [s, r] [= A -> A_prop [s, r].
Proof.
  A_simpl.
  intros H; apply A_above_sound.
  (* TODO reason about pairs and least fixed points *)
Admitted.
