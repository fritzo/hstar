(** * A constructor for polymorphic types *)

Require Import Coq.Program.Basics.
Require Import Coq.Setoids.Setoid.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Export InformationOrdering.
Require Import Nontermination.
Require Import LeastFixedPoint.
Require Import BohmTrees.
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

Lemma pair_extensionality (Var : Set) (x y x' y' : Code Var) :
  <<x, y>> [= <<x', y'>> <-> x [= x' /\ y [= y'.
Proof.
  unfold pair; beta_simpl; split.
    intro H; split.
      apply (code_le_ap_left _ _ _ K) in H; beta_simpl in H; auto.
    apply (code_le_ap_left _ _ _ (K*I)) in H; beta_simpl in H; auto.
  intros [Hx Hy]; auto.
Qed.

Definition sub_pair {Var : Set} (x : Code Var) := x [= <<TOP, TOP>>.

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

Lemma sub_pair_pair (Var : Set) (x y : Code Var) : sub_pair <<x, y>>.
Proof.
  unfold sub_pair, pair; eta_expand as f; beta_reduce.
  monotonicity; auto.
Qed.

(* FIXME is this true? *)
Definition sub_pair_elim_intro {Var : Set} (x : Code Var) :
  sub_pair x -> x [= <<x*K, x*(K*I)>>.
Proof.
  unfold sub_pair, pair; simpl.
  intros H. (* eta_expand in H. FIXME eta_expand is borken *)
  eta_expand as f; beta_reduce.
Admitted.

Definition A_prop {Var : Set} (a : Code Var) :=
  sub_pair a /\ forall s r, <<s, r>> [= a -> r o s [= I.

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
  unfold A_prop; unfold sub_pair; split ;
  [ try apply pair_extensionality; auto
  | intros s r H;
    apply pair_extensionality in H;
    destruct H as [Hs Hr];
    rewrite Hs; rewrite Hr
  ].

Lemma A_I_I (Var : Set) : A_prop (<<I, I>> : Code Var).
Proof. A_prop_pair; beta_eta. Qed.
Hint Resolve A_I_I.

Section raise.
  Context {Var : Set}.
  Let x := make_var Var 3.
  Let y := make_var Var 4.

  Definition raise := Eval compute in close (\x, \y, x).
  Definition lower := Eval compute in close (\x, x * TOP).

  Definition pull := Eval compute in close (\x, \y, x || div * y).
  Definition push := Eval compute in close (\x, x * BOT).

  Lemma lower_raise : lower o raise == I.
  Proof. unfold lower, raise; beta_eta. Qed.

  Lemma push_pull : push o pull == I.
  Proof.
    unfold push, pull; eta_expand; beta_simpl.
    symmetry; apply code_le_eq_j.
    fold (@div Var); code_simpl; auto.
  Qed.

  Lemma A_raise_lower : A_prop <<raise, lower>>.
  Proof. A_prop_pair; apply lower_raise. Qed.

  Lemma A_pull_push : A_prop <<pull, push>>.
  Proof. A_prop_pair; apply push_pull. Qed.
End raise.
Hint Resolve A_raise_lower.
Hint Resolve A_pull_push.

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

Definition A_step {Var : Set} : Code Var
  := K * <<I, I>>
  || K * <<raise, lower>>
  || K * <<pull, push>>
  || compose
  || conjugate.

Definition A {Var : Set} : Code Var := Eval compute in Y * A_step.

Lemma A_simpl (Var : Set) : (A : Code Var) == Y * A_step.
Proof.
  (freeze code_eq in compute); auto.
Qed.

Ltac A_simpl := rewrite A_simpl; unfold A_step.

Notation "\\ x , y ; z" := (A * \x, \y, z)%code : code_scope.

Section A_example.
  Variable Var : Set.
  Let a := make_var Var 0.
  Let a' := make_var Var 1.
  Let A_example : Code Var := close (\\a,a'; a --> a').
End A_example.

Inductive A_above {Var : Set} : Code Var -> Prop :=
  | A_above_below x y : x [= y -> A_above y -> A_above x
  | A_above_i_i : A_above <<I, I>>
  | A_above_raise_lower : A_above <<raise, lower>>
  | A_above_pull_push : A_above <<pull, push>>
  | A_above_compose a : A_above a -> A_above (compose * a)
  | A_above_conjugate a : A_above a -> A_above (conjugate * a).

Instance A_above_le (Var : Set) : Proper (code_le --> impl) (@A_above Var).
Proof.
  intros x x' xx' H; apply A_above_below with x; auto.
Qed.

Instance A_above_eq (Var : Set) : Proper (code_eq ==> iff) (@A_above Var).
Proof.
  split; destruct H as [Hl Hr]; apply A_above_le; auto.
Qed.

Lemma A_above_A (Var : Set) (a : Code Var) : a [= A <-> A_above a.
Proof.
  (* TODO this needs some sort of least-fixed-point lemma *)
Admitted.

Lemma A_sound (Var : Set) (r s : Code Var) : <<s, r>> [= A -> A_prop <<s, r>>.
Proof.
  intros H; apply A_above_A in H.
  induction H; auto.
  rewrite H; auto.
Qed.

(** ** A strong characterization of [A] *)

Lemma A_pair (Var : Set) : (A : Code Var) [= <<TOP, TOP>>.
Proof.
  (* TODO *)
Admitted.

Lemma A_complete (Var : Set) (s r : Code Var) : r o s [= I -> <<s, r>> [= A.
Proof.
  A_simpl; intro Hi.
  (* OLD
  apply Join_lub; unfold is_upper_bound.
  intros sr; induction sr as [[s r] Hless].
  apply LESS_conv.
  intros c Hdef Hconv.
  inversion Hconv.
  *)
Admitted.

Theorem A_implicit (Var : Set) (x f : Code Var) :
  x [= A * f <-> (forall s r : Code Var, r o s [= I -> x [= f * s * r).
Proof.
Admitted.
