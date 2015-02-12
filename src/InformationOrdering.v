(** * Information ordering and observable equivalence *)

Require Import Coq.Logic.Classical_Prop.
Require Import Coq.Program.Basics.
Require Import Coq.Program.Equality.
Require Import Coq.Setoids.Setoid.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Lists.List.
Require Export Convergence.
Open Scope term_scope.

Definition term_le {Var : Set} (x y : Term Var) :=
  forall (Var' : Set) (c : Term Var') (f : Var -> Term Var'),
  conv (c * (x @ f)) -> conv (c * (y @ f)).
Notation "x [= y" := (term_le x y) : term_scope.

Definition term_eq {Var : Set} (x y : Term Var) := x [= y /\ y [= x.
Notation "x == y" := (term_eq x y) : term_scope.

Instance term_le_eq_subrelation (Var : Set) :
  subrelation (@term_eq Var) (@term_le Var).
Proof.
  unfold subrelation, predicate_implication, pointwise_lifting.
  unfold term_eq; intros x y [xy yx]; auto.
Qed.

Instance term_le_beta_proper (Var : Set) :
  Proper (beta ==> beta ==> iff) (@term_le Var).
Proof.
  intros x x' Hx y y' Hy; split; unfold term_le; intros Hle Var' c f Hc.
    rewrite <- Hy; apply Hle; rewrite -> Hx; auto.
  rewrite -> Hy; apply Hle; rewrite <- Hx; auto.
Qed.

Instance term_eq_beta_proper (Var : Set) :
  Proper (beta ==> beta ==> iff) (@term_eq Var).
Proof.
  unfold term_eq.
  intros x x' xx' y y' yy'; split; intros [xy yx].
    split; rewrite <- xx'; rewrite <- yy'; auto.
  split; rewrite -> xx'; rewrite -> yy'; auto.
Qed.

Lemma term_le_beta (Var : Set) (x y : Term Var) : beta x y -> x [= y.
Proof.
  unfold term_le; intros H Var' c f Hc.
  rewrite <- H; auto.
Qed.
Hint Resolve term_le_beta.

Instance term_le_beta_subrelation (Var : Set) :
  subrelation beta (@term_le Var).
Proof.
  intros x y H; apply term_le_beta; auto.
Qed.

Lemma term_eq_beta (Var : Set) (x y : Term Var) : beta x y -> x == y.
Proof.
  unfold term_le; intro H; split; intros Var' c f Hc.
  rewrite <- H; auto.
  rewrite -> H; auto.
Qed.
Hint Resolve term_eq_beta.

Instance term_eq_beta_subrelation (Var : Set) :
  subrelation beta (@term_eq Var).
Proof.
  simpl_relation; apply term_eq_beta; auto.
Qed.

Instance term_le_proper_pi (Var : Set) :
  Proper (pi ++> pi --> impl) (@term_le Var).
Proof.
  intros x x' Hx y y' Hy; unfold term_le; intros Hle Var' c f Hc.
  unfold flip in *.
  rewrite Hy.
  apply Hle; rewrite -> Hx; auto.
Qed.

Instance term_le_pi_subrelation (Var : Set) :
  subrelation (inverse pi) (@term_le Var).
Proof.
  unfold subrelation, predicate_implication, pointwise_lifting, flip.
  intros x y H; unfold term_le; intros Var' c f Hc.
  rewrite -> H; auto.
Qed.

Instance term_le_refl (Var : Set) : Reflexive (@term_le Var).
Proof.
  unfold term_le; auto.
Qed.

Instance term_eq_refl (Var : Set) : Reflexive (@term_eq Var).
Proof.
  simpl_relation.
Qed.

Instance term_le_trans (Var : Set) : Transitive (@term_le Var).
Proof.
  unfold term_le; auto.
Qed.

Instance term_eq_trans (Var : Set) : Transitive (@term_eq Var).
Proof.
  unfold term_eq, term_le; simpl_relation.
Qed.

Instance term_eq_sym (Var : Set) : Symmetric (@term_eq Var).
Proof.
  unfold term_eq, term_le; simpl_relation.
Qed.

Instance term_le_preorder (Var : Set) : PreOrder (@term_le Var).
Proof.
  split; [apply term_le_refl | apply term_le_trans].
Qed.

Instance term_eq_equivalence (Var : Set) : Equivalence (@term_eq Var).
Proof.
  split; [apply term_eq_refl | apply term_eq_sym | apply term_eq_trans].
Qed.

Instance term_le_partialorder (Var : Set) :
  PartialOrder (@term_eq Var) (@term_le Var).
Proof.
  simpl_relation.
Qed.

Lemma term_le_ap_right (Var : Set) (x y y' : Term Var) :
  y [= y' -> x * y [= x * y'.
Proof.
  unfold term_le; intros H Var' c f.
  repeat rewrite term_sub_ap.
  intros Hconv.
  admit.
  (* OLD
  rewrite <- beta_b.
  apply H.
  rewrite -> beta_b.
  auto.
  *)
Qed.
Hint Resolve term_le_ap_right.

Lemma term_le_ap_left (Var : Set) (x x' y : Term Var) :
  x [= x' -> x * y [= x' * y.
Proof.
  unfold term_le; intros H Var' c f.
  repeat rewrite term_sub_ap.
  intros Hconv.
  admit.
  (* OLD
  rewrite <- (beta_right (beta_left beta_i)).
  rewrite <- (beta_right beta_c).
  rewrite <- beta_b.
  apply H.
  rewrite -> beta_b.
  rewrite -> (beta_right beta_c).
  rewrite -> (beta_right (beta_left beta_i)).
  auto.
  *)
Qed.
Hint Resolve term_le_ap_left.

Lemma term_le_ap (Var : Set) (x x' y y' : Term Var) :
  x [= x' -> y [= y' -> x * y [= x' * y'.
Proof.
  intros Hx Hy; transitivity (x * y'); auto.
Qed.
Hint Resolve term_le_ap.

Lemma term_eq_ap_right (Var : Set) (x y y' : Term Var) :
  y == y' -> x * y == x * y'.
Proof.
  unfold term_eq; intros [H H']; split; auto.
Qed.
Hint Resolve term_eq_ap_right.

Lemma term_eq_ap_left (Var : Set) (x x' y : Term Var) :
  x == x' -> x * y == x' * y.
Proof.
  unfold term_eq; intros [H H']; split; auto.
Qed.
Hint Resolve term_eq_ap_left.

Lemma term_eq_ap (Var : Set) (x x' y y' : Term Var) :
  x == x' -> y == y' -> x * y == x' * y'.
Proof.
  intros Hx Hy; transitivity (x * y'); auto.
Qed.
Hint Resolve term_eq_ap.

Instance term_ap_le (Var : Set) :
  Proper (term_le ==> term_le ==> term_le) (@APP Var).
Proof.
  intros x x' Hx y y' Hy.
  apply term_le_trans with (x * y'); auto.
Qed.

Instance term_ap_eq (Var : Set) :
  Proper (term_eq ==> term_eq ==> term_eq) (@APP Var).
Proof.
  intros x x' Hx y y' Hy.
  apply term_eq_trans with (x * y'); auto.
Qed.

Ltac term_le_monotonicity := repeat ((
  apply term_le_ap_left ||
  apply term_le_ap_right ||
  apply term_le_ap) ; auto).

Ltac term_eq_monotonicity := repeat (
  apply term_eq_ap_left ||
  apply term_eq_ap_right ||
  apply term_eq_ap).

Ltac monotonicity :=
  match goal with
  | [|- _ [= _] => term_le_monotonicity
  | [|- _ == _] => term_eq_monotonicity
  end.

Instance conv_proper_le (Var : Set) : Proper (term_le ++> impl) (@conv Var).
Proof.
  intros x y Hxy Hc; unfold term_le in Hxy.
  admit.
  (* OLD
  rewrite <- var_monad_unit_right; rewrite <- beta_i.
  apply Hxy; term_simpl; auto.
  *)
Qed.

Instance conv_proper_eq (Var : Set) : Proper (term_eq ==> iff) (@conv Var).
Proof.
  intros x y [Hxy Hyx]; split; intro Hc;
  [rewrite <- Hxy | rewrite <- Hyx]; auto.
Qed.

Lemma term_sub_le_left
  (Var Var' : Set) (f g : Var -> Term Var') (x : Term Var) :
  (forall v, f v [= g v) -> x @ f [= x @ g.
Proof.
  induction x; intros; try (simpl; auto; reflexivity).
  - admit.
  - admit.
  - admit.
Qed.

Lemma term_sub_le_right
  (Var Var' : Set) (f : Var -> Term Var') (x y : Term Var) :
  x [= y -> x @ f [= y @ f.
Proof.
  intros H Var'' c f'; repeat rewrite var_monad_assoc; auto.
Qed.

Instance term_sub_proper_le (Var Var' : Set) :
  Proper ((eq ==> term_le) ==> term_le ==> term_le) (@term_sub Var Var').
Proof.
  intros f g Hfg x y Hxy; transitivity (y @ f);
  [apply term_sub_le_right | apply term_sub_le_left]; auto.
Qed.

Lemma term_sub_le {Var Var' : Set} (f : Var -> Term Var') (x y : Term Var) :
  x [= y -> x @ f [= y @ f.
Proof.
  intro xy; rewrite xy; reflexivity.
Qed.

Instance term_sub_proper_eq (Var Var' : Set) :
  Proper ((eq ==> term_eq) ==> term_eq ==> term_eq) (@term_sub Var Var').
Proof.
  intros f g Hfg x y Hxy; transitivity (y @ f); split.
  - rewrite Hxy; auto.
  - rewrite <- Hxy; auto.
  - rewrite Hfg; auto.
  - rewrite <- Hfg; auto.
Qed.

Lemma term_sub_eq {Var Var' : Set} (f : Var -> Term Var') (x y : Term Var) :
  x == y -> x @ f == y @ f.
Proof.
  intro xy; rewrite xy; reflexivity.
Qed.

Lemma term_le_top (Var : Set) (x : Term Var) : x [= TOP.
Proof.
  intros; rewrite (pi_top x); auto.
Qed.
Hint Resolve term_le_top.

Lemma term_le_bot (Var : Set) (x : Term Var) : BOT [= x.
Proof.
  unfold term_le; intros Var' c f Hred.
  simpl in Hred.
  rewrite -> (pi_app_right (pi_bot _)).
  auto.
Qed.
Hint Resolve term_le_bot.

Lemma absolute_consistency (Var : Set) : ~ TOP [= (BOT : Term Var).
Proof.
  intro H; unfold term_le in H.
  apply (@not_conv_bot Var).
  admit.
  (* OLD
  rewrite <- beta_i; rewrite <- var_monad_unit_right.
  apply H; term_simpl; auto.
  *)
Qed.
Hint Resolve absolute_consistency.

(** ** Basic properties of information ordering *)

Lemma term_le_j_left (Var : Set) (x y : Term Var) : x [= x || y.
Proof.
  unfold term_le; intros Var' c f Hred.
  rewrite pi_j_left; auto.
Qed.
Hint Resolve term_le_j_left.

Lemma term_le_j_right (Var : Set) (x y : Term Var) : y [= x || y.
Proof.
  unfold term_le; intros Var' c f Hred.
  rewrite pi_j_right; auto.
Qed.
Hint Resolve term_le_j_right.

Lemma term_le_j_ub (Var : Set) (x y z : Term Var) :
  x [= z -> y [= z -> x || y [= z.
Proof.
  unfold term_le; intros Hx Hy Var' c f Hc.
Admitted.
Hint Resolve term_le_j_ub.

Lemma term_le_join (Var : Set) (x y z : Term Var) :
  x || y [= z <-> x [= z /\ y [= z.
Proof.
  split; intro H.
    split; apply term_le_trans with (x || y); auto.
  destruct H as [Hx Hy]; auto.
Qed.
Hint Resolve term_le_join.

Lemma term_le_eq_j (Var : Set) (x y : Term Var) : x [= y <-> y == y || x.
Proof.
  split; intro H; [split | rewrite H]; auto.
Qed.

Lemma term_le_j_idem (Var : Set) (x : Term Var) : x||x [= x.
Proof.
  apply term_le_join; split; reflexivity.
Qed.
Hint Resolve term_le_j_idem.

Lemma term_eq_j_idem (Var : Set) (x : Term Var) : x||x == x.
Proof.
  split; auto.
Qed.
Hint Resolve term_eq_j_idem.

Lemma term_le_j_sym (Var : Set) (x y : Term Var) : x||y == y||x.
Proof.
  split; auto.
Qed.

Lemma term_eq_j_assoc (Var : Set) (x y z : Term Var) : x||(y||z) == (x||y)||z.
Proof.
  split; auto.
  - apply term_le_j_ub; auto.
    transitivity (x||y); auto.
    admit. (* TODO prove join_proper_le *)
  - apply term_le_j_ub; auto.
      admit. (* TODO prove join_proper_le *)
    transitivity (y||z); auto.
Qed.

Lemma term_le_j_ap_right (Var : Set) (f x y : Term Var) :
  f * x || f * y [= f * (x || y).
Proof.
  apply term_le_join; split; monotonicity.
Qed.

Lemma term_le_j_bot_left (Var : Set) (x : Term Var) : BOT || x == x.
Proof.
  split; auto.
Qed.
Hint Rewrite term_le_j_bot_left : term_simpl.

Lemma term_le_j_bot_right (Var : Set) (x : Term Var) : x || BOT == x.
Proof.
  split; auto.
Qed.
Hint Rewrite term_le_j_bot_right : term_simpl.

Lemma term_le_j_top_left (Var : Set) (x : Term Var) : TOP || x == TOP.
Proof.
  split; auto.
Qed.
Hint Rewrite term_le_j_top_left : term_simpl.

Lemma term_le_j_top_right (Var : Set) (x : Term Var) : x || TOP == TOP.
Proof.
  split; auto.
Qed.
Hint Rewrite term_le_j_top_right : term_simpl.

(** ** Reasoning with extensionality *)

(*
Ltac abstract M x :=
  match m with
  | x => APP term_i x
  | APP ?M1 ?M2 =>
    let APP N1 _ := abstract M1 x in
    let APP N2 _ := abstract M2 x in
    APP (APP (APP term_s N1) N2) x
  | _ => APP term_k x
  end.

Ltac beta_subs :=
  match goal with
  | beta x y
*)

Lemma term_le_extensionality (Var : Set) (x x' : Term Var) :
  (forall y, x * y [= x' * y) -> x [= x'.
Proof.
  unfold term_le; intros H Var' c f Hconv.
  (* TODO implement via abstraction algorithm *)
Admitted.

Lemma term_eq_extensionality (Var : Set) (x x' : Term Var) :
  (forall y, x * y == x' * y) -> x == x'.
Proof.
  intro H; split; apply term_le_extensionality; apply H.
Qed.

Tactic Notation "eta_expand" :=
  let x := fresh in
  match goal with
  | [|- _ [= _] => apply term_le_extensionality; intro x
  | [|- _ == _] => apply term_eq_extensionality; intro x
  end.

Tactic Notation "eta_expand" "as" ident(x) :=
  match goal with
  | [|- _ [= _] => apply term_le_extensionality; intro x
  | [|- _ == _] => apply term_eq_extensionality; intro x
  end.

Tactic Notation "eta_expand" "in" hyp(H) :=
  eapply term_le_ap_left in H; beta_reduce in H.

Ltac beta_eta :=
  beta_reduce; auto
  || eta_expand; beta_reduce; auto
  || eta_expand; eta_expand; beta_reduce; auto
  || eta_expand; eta_expand; eta_expand; beta_reduce; auto.

Lemma term_eq_ap_top (Var : Set) (x : Term Var) : TOP * x == TOP.
Proof.
  split; auto.
  rewrite (pi_top (K * TOP : Term Var)) at 2; unfold K;
  simpl; beta_reduce; simpl; auto.
  admit. (* TODO yuck *)
Qed.
Hint Rewrite term_eq_ap_top : term_simpl.

Lemma term_eq_b_i (Var : Set) (x : Term Var) : I o x == x.
Proof.
  admit.
  (* OLD
  beta_eta.
  *)
Qed.
Hint Rewrite term_eq_b_i : term_simpl.

Lemma term_eq_c_b_i (Var : Set) (x : Term Var) : x o I == x.
Proof.
  admit.
  (* OLD
  beta_eta.
  *)
Qed.
Hint Rewrite term_eq_b_i : term_simpl.

Lemma term_eq_s_k_b (Var : Set) (x : Term Var) : S * (K * x) == B * x.
Proof.
  admit.
  (* OLD
  beta_eta.
  *)
Qed.
Hint Rewrite term_eq_s_k_b : term_simpl.

Lemma term_eq_s_k_c (Var : Set) (x y : Term Var) :
  S * x * (K * y) == C * x * y.
Proof.
  admit.
  (* OLD
  beta_eta.
  *)
Qed.
Hint Rewrite term_eq_s_k_c : term_simpl.

(** We will use classical reasoning for case analysis. *)

Lemma case_le (Var : Set) (x y : Term Var) (p : Prop) :
  (x [= y -> p) -> (~ x [= y -> p) -> p.
Proof.
  intros H H'; elim (classic (x [= y)); auto.
Qed.

Tactic Notation "case_le" constr(xy) :=
  match xy with
  | ?x [= ?y => apply (@case_le _ x y _)
  end; intro.

Tactic Notation "case_le" constr(xy) "as" ident(H) :=
  match xy with
  | ?x [= ?y => apply (@case_le _ x y _)
  end; intro H.

(** ** Simpler versions of convergence and ordering  *)

Fixpoint term_apply {Var : Set} (x : Term Var) (ys : list (Term Var)) :
  Term Var :=
  match ys with
  | nil => x
  | (y ::ys')%list => term_apply (x * y) ys'
  end.

Notation "x ** y" := (term_apply x y) : term_scope.

Instance term_apply_proper_le (Var : Set) :
  Proper (term_le ==> eq ==> term_le) (@term_apply Var).
Proof.
  intros x x' xx' y y' yy'; subst.
  revert x x' xx'; induction y'; simpl; auto.
Qed.

Instance term_apply_proper_eq (Var : Set) :
  Proper (term_eq ==> eq ==> term_eq) (@term_apply Var).
Proof.
  intros x x' [xx' x'x] y y' yy'; subst; split;
  [rewrite xx' | rewrite x'x]; auto.
Qed.

Fixpoint term_repeat {Var : Set} (x : Term Var) (n : nat) : list (Term Var) :=
  match n with
  | 0 => nil
  | Succ n' => (x :: term_repeat x n')%list
  end.

Notation "x ^^ n" := (term_repeat x n) : term_scope.

Fixpoint term_tuple {Var : Set} (ys : list (Term Var)) : Term Var :=
  match ys with
  | nil => I
  | (y :: ys')%list => term_tuple ys' o (C * I * y)
  end.

Lemma beta_tuple_apply (Var : Set) (ys : list (Term Var)) :
  forall x : Term Var, beta (term_tuple ys * x) (x ** ys).
Proof.
  induction ys; simpl; auto; intro x.
  - unfold I; beta_reduce; compute; reflexivity.
  - unfold C, I, B; beta_reduce; compute.
    admit.
Qed.
Hint Resolve beta_tuple_apply.

Instance term_tuple_le (Var : Set) :
  Proper (Forall2 term_le ==> term_le) (@term_tuple Var).
Proof.
  intros xs xs' xsxs'; induction xsxs'; simpl; auto.
Qed.

Lemma term_repeat_commute_1 (Var : Set) (x y : Term Var) (n : nat) :
  (x * y) ** y ^^ n = (x ** y ^^ n) * y.
Proof.
  revert x y; induction n; simpl; auto.
Qed.

Lemma term_repeat_top (Var : Set) (ys : list (Term Var)) :
  Forall2 term_le ys (TOP ^^ length ys).
Proof.
  induction ys; simpl; auto.
Qed.
Hint Resolve term_repeat_top.

Lemma ap_top_conv (Var : Set) (x : Term Var) : conv x <-> conv (x * TOP).
Proof.
  assert (probe x (x * TOP)) as eq; auto.
  rewrite <- eq; reflexivity.
Qed.

Definition weak_term_le {Var : Set} (x x' : Term Var) : Prop :=
  forall (ys : list (Term Empty_set)) (f : Var -> Term Empty_set),
  conv ((x @ f) ** ys) -> conv ((x' @ f) ** ys).

Lemma weak_term_le_complete (Var : Set) (x x' : Term Var) :
  x [= x' -> weak_term_le x x'.
Proof.
  unfold term_le; intros H ys f Hconv.
  rewrite <- beta_tuple_apply; apply H.
  rewrite beta_tuple_apply; auto.
Qed.

Lemma weak_term_le_sound (Var : Set) (x x' : Term Var) :
  weak_term_le x x' -> x [= x'.
Proof.
  unfold term_le; intros H Var' c f Hconv.
  assert (forall (ys : list (Term Var')),
    conv ((x @ f) ** ys) -> conv ((x' @ f) ** ys)) as H'; auto; clear H.
  set (y := x @ f) in *; set (y' := x' @ f) in *.
  inversion Hconv; simpl; auto.
  (* TODO maybe prove by induction on BT of c? *)
Admitted.

Theorem term_le_weaken (Var : Set) (x x' : Term Var) :
  x [= x' <-> weak_term_le x x'.
Proof.
  split; [apply weak_term_le_complete | apply weak_term_le_sound].
Qed.

Ltac term_le_weaken := apply term_le_weaken; unfold weak_term_le.

Lemma conv_ap (Var : Set) (x a : Term Var) : conv (x * a) -> conv x.
Proof.
  rewrite (term_le_top _ a).
  intros [y [xy yt]].
  exists y; split; auto.
  unfold close in xy; simpl in xy; fold (@close Var) in xy.
  transitivity ((close x) * TOP); auto.
Qed.

Lemma conv_apply (Var : Set) (x : Term Var) (ys : list (Term Var)) :
  conv (x ** ys) -> conv x.
Proof.
  revert x; induction ys; simpl; intros; eauto using conv_ap.
Qed.
