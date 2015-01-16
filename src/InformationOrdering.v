(** * Information ordering and observable equivalence *)

Require Import Coq.Program.Basics.
Require Import Coq.Setoids.Setoid.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Lists.List.
Require Export Codes.
Open Scope code_scope.

Definition code_le {Var : Set} (x y : Code Var) :=
  forall (Var' : Set) (c : Code Var') (f : Var -> Code Var'),
  conv (c * (x @ f)) -> conv (c * (y @ f)).
Notation "x [= y" := (code_le x y)%code : code_scope.

Definition code_eq {Var : Set} (x y : Code Var) := x [= y /\ y [= x.
Notation "x == y" := (code_eq x y)%code : code_scope.

Instance code_le_eq_subrelation (Var : Set) :
  subrelation (@code_eq Var) (@code_le Var).
Proof.
  unfold subrelation, predicate_implication, pointwise_lifting.
  unfold code_eq; intros x y [xy yx]; auto.
Qed.

Instance code_le_beta_proper (Var : Set) :
  Proper (beta ==> beta ==> iff) (@code_le Var).
Proof.
  intros x x' Hx y y' Hy; split; unfold code_le; intros Hle Var' c f Hc.
    rewrite <- Hy; apply Hle; rewrite -> Hx; auto.
  rewrite -> Hy; apply Hle; rewrite <- Hx; auto.
Qed.

Instance code_eq_beta_proper (Var : Set) :
  Proper (beta ==> beta ==> iff) (@code_eq Var).
Proof.
  unfold code_eq.
  intros x x' xx' y y' yy'; split; intros [xy yx].
    split; rewrite <- xx'; rewrite <- yy'; auto.
  split; rewrite -> xx'; rewrite -> yy'; auto.
Qed.

Lemma code_le_beta (Var : Set) (x y : Code Var) : beta x y -> x [= y.
Proof.
  unfold code_le; intros H Var' c f Hc.
  rewrite <- H; auto.
Qed.
Hint Resolve code_le_beta.

Instance code_le_beta_subrelation (Var : Set) :
  subrelation beta code_le := code_le_beta Var.

Lemma code_eq_beta (Var : Set) (x y : Code Var) : beta x y -> x == y.
Proof.
  unfold code_le; intro H; split; intros Var' c f Hc.
  rewrite <- H; auto.
  rewrite -> H; auto.
Qed.
Hint Resolve code_eq_beta.

Instance code_eq_beta_subrelation (Var : Set) :
  subrelation beta code_eq := code_eq_beta Var.

Instance code_le_pi_proper (Var : Set) :
  Proper (pi ++> pi --> impl) (@code_le Var).
Proof.
  intros x x' Hx y y' Hy; unfold code_le; intros Hle Var' c f Hc.
  unfold flip in *.
  rewrite (pi_ap_right (code_sub_pi_right _ _ _ _ _ Hy)).
  apply Hle. rewrite -> Hx. auto.
Qed.

Instance code_le_pi_subrelation (Var : Set) :
  subrelation (inverse pi) (@code_le Var).
Proof.
  unfold subrelation, predicate_implication, pointwise_lifting, flip.
  intros x y H; unfold code_le; intros Var' c f Hc.
  rewrite -> H; auto.
Qed.

Instance code_le_refl (Var : Set) : Reflexive (@code_le Var).
Proof. unfold code_le; auto. Qed.

Instance code_eq_refl (Var : Set) : Reflexive (@code_eq Var).
Proof. simpl_relation. Qed.

Instance code_le_trans (Var : Set) : Transitive (@code_le Var).
Proof. unfold code_le; auto. Qed.

Instance code_eq_trans (Var : Set) : Transitive (@code_eq Var).
Proof.
  unfold code_eq, code_le; simpl_relation.
Qed.

Instance code_eq_sym (Var : Set) : Symmetric (@code_eq Var).
Proof.
  unfold code_eq, code_le; simpl_relation.
Qed.

Instance code_le_preorder (Var : Set) : PreOrder (@code_le Var).
Proof.
  split; [apply code_le_refl | apply code_le_trans].
Qed.

Instance code_eq_equivalence (Var : Set) : Equivalence (@code_eq Var).
Proof.
  split; [apply code_eq_refl | apply code_eq_sym | apply code_eq_trans].
Qed.

Instance code_le_partialorder (Var : Set) :
  PartialOrder (@code_eq Var) (@code_le Var).
Proof. simpl_relation. Qed.

Lemma code_le_ap_right (Var : Set) (x y y' : Code Var) :
  y [= y' -> x * y [= x * y'.
Proof.
  (* OLD
  unfold code_le, conv; intros H Var' c f.
  repeat rewrite code_sub_ap.
  intros Hconv.
  rewrite <- (beta_ap_right beta_b); apply H.
  rewrite -> (beta_ap_right beta_b); auto.
  *)
Admitted.
Hint Resolve code_le_ap_right.

Lemma code_le_ap_left (Var : Set) (x x' y : Code Var) :
  x [= x' -> x * y [= x' * y.
Proof.
  (* OLD
  unfold code_le, conv; intros H Var' c f.
  repeat rewrite code_sub_ap.
  intros Hconv.
  rewrite <- (beta_ap_right (beta_ap_right (beta_ap_left beta_i))).
  rewrite <- (beta_ap_right (beta_ap_right beta_c)).
  rewrite <- (beta_ap_right beta_b).
  apply H.
  rewrite -> (beta_ap_right beta_b).
  rewrite -> (beta_ap_right (beta_ap_right beta_c)).
  rewrite -> (beta_ap_right (beta_ap_right (beta_ap_left beta_i))).
  auto.
  *)
Admitted.
Hint Resolve code_le_ap_left.

Lemma code_le_ap (Var : Set) (x x' y y' : Code Var) :
  x [= x' -> y [= y' -> x * y [= x' * y'.
Proof.
  intros Hx Hy; transitivity (x * y'); auto.
Qed.
Hint Resolve code_le_ap.

Lemma code_eq_ap_right (Var : Set) (x y y' : Code Var) :
  y == y' -> x * y == x * y'.
Proof.
  unfold code_eq; intros [H H']; split; auto.
Qed.
Hint Resolve code_eq_ap_right.

Lemma code_eq_ap_left (Var : Set) (x x' y : Code Var) :
  x == x' -> x * y == x' * y.
Proof.
  unfold code_eq; intros [H H']; split; auto.
Qed.
Hint Resolve code_eq_ap_left.

Lemma code_eq_ap (Var : Set) (x x' y y' : Code Var) :
  x == x' -> y == y' -> x * y == x' * y'.
Proof.
  intros Hx Hy; transitivity (x * y'); auto.
Qed.
Hint Resolve code_eq_ap.

Instance code_ap_le (Var : Set) :
  Proper (code_le ==> code_le ==> code_le) (@code_ap Var).
Proof.
  intros x x' Hx y y' Hy.
  apply code_le_trans with (x * y'); auto.
Qed.

Instance code_ap_eq (Var : Set) :
  Proper (code_eq ==> code_eq ==> code_eq) (@code_ap Var).
Proof.
  intros x x' Hx y y' Hy.
  apply code_eq_trans with (x * y'); auto.
Qed.

Ltac code_le_monotonicity := repeat ((
  apply code_le_ap_left ||
  apply code_le_ap_right ||
  apply code_le_ap) ; auto).

Ltac code_eq_monotonicity := repeat (
  apply code_eq_ap_left ||
  apply code_eq_ap_right ||
  apply code_eq_ap).

Ltac monotonicity :=
  match goal with
  | [|- _ [= _] => code_le_monotonicity
  | [|- _ == _] => code_eq_monotonicity
  end.

Instance code_abs_le (Var Var' : Set) (b : Var -> option Var') :
  Proper (code_le ==> code_le) (code_abs b).
Proof.
  intros x x' Hx.
Admitted.

Instance code_abs_eq (Var Var' : Set) (b : Var -> option Var') :
  Proper (code_eq ==> code_eq) (code_abs b).
Proof.
  intros x x' Hx.
Admitted.

Instance code_close_le (Var : Set) : Proper (code_le ==> code_le) (@close Var).
Proof.
  intros x x' xx'.
Admitted.

Instance code_close_eq (Var : Set) : Proper (code_eq ==> code_eq) (@close Var).
Proof.
  intros x x' xx'.
Admitted.

Lemma code_le_top_closed (x : Code Empty_set) : x [= TOP.
Proof.
  (* OLD
  unfold code_le, conv.
  induction x; intros Var' c f;
  intro Hc; inversion Hc as [? y ? Hb Hp e1 e2]; clear e1 e2; auto.
    inversion v.
    admit. (* easy context twiddling *)
  *)
Admitted.

Lemma code_le_top (Var : Set) (x : Code Var) : x [= TOP.
Proof.
  (* OLD
  unfold code_le, conv ; intros Var' c f Hred.
  simpl.
  rewrite <- beta_b.
  *)
  (* OLD
  rewrite -> (pi_top (x @ f)) at 1.
  rewrite -> beta_b; auto.
  *)
Admitted.
Hint Resolve code_le_top.

Lemma code_le_bot (Var : Set) (x : Code Var) : BOT [= x.
Proof.
  (* OLD
  unfold code_le, conv; intros Var' c f Hred.
  rewrite <- beta_b.
  rewrite -> (pi_ap_right (pi_bot _)).
  rewrite -> beta_b; auto.
  *)
Admitted.
Hint Resolve code_le_bot.

(** ** Basic properties of information ordering *)

Lemma code_le_j_left (Var : Set) (x y : Code Var) : x [= x || y.
Proof.
  (* OLD
  unfold code_le, conv; intros Var' c f Hred.
  rewrite pi_j_left; auto.
  *)
Admitted.
Hint Resolve code_le_j_left.

Lemma code_le_j_right (Var : Set) (x y : Code Var) : y [= x || y.
Proof.
  (* OLD
  unfold code_le, conv; intros Var' c f Hred.
  rewrite pi_j_right; auto.
  *)
Admitted.
Hint Resolve code_le_j_right.

Lemma code_le_j_ub (Var : Set) (x y z : Code Var) :
  x [= z -> y [= z -> x || y [= z.
Proof.
  (* OLD
  unfold code_le, conv; intros Hx Hy Var' c f Hconv.
  *)
Admitted.
Hint Resolve code_le_j_ub.

Lemma code_le_join (Var : Set) (x y z : Code Var) :
  x || y [= z <-> x [= z /\ y [= z.
Proof.
  split; intro H.
    split; apply code_le_trans with (x || y); auto.
  destruct H as [Hx Hy]; auto.
Qed.
Hint Resolve code_le_join.

Lemma code_le_eq_j (Var : Set) (x y : Code Var) : x [= y <-> y == y || x.
Proof.
  split; intro H; [split | rewrite H]; auto.
Qed.

Lemma code_le_j_idem (Var : Set) (x : Code Var) : x||x [= x.
Proof.
  apply code_le_join; split; reflexivity.
Qed.
Hint Resolve code_le_j_idem.

Lemma code_eq_j_idem (Var : Set) (x : Code Var) : x||x == x.
Proof. split; auto. Qed.
Hint Resolve code_eq_j_idem.

Lemma code_le_j_sym (Var : Set) (x y : Code Var) : x||y == y||x.
Proof. split; auto. Qed.

Lemma code_le_j_assoc (Var : Set) (x y z : Code Var) : x||(y||z) == (x||y)||z.
Proof.
  split; auto.
    apply code_le_j_ub; auto.
    transitivity (x||y); auto.
  apply code_le_j_ub; auto.
  transitivity (y||z); auto.
Qed.

Lemma code_le_j_bot_left (Var : Set) (x : Code Var) : BOT || x == x.
Proof. split; auto. Qed.
Hint Rewrite code_le_j_bot_left : code_simpl.

Lemma code_le_j_bot_right (Var : Set) (x : Code Var) : x || BOT == x.
Proof. split; auto. Qed.
Hint Rewrite code_le_j_bot_right : code_simpl.

Lemma code_le_j_top_left (Var : Set) (x : Code Var) : TOP || x == TOP.
Proof. split; auto. Qed.
Hint Rewrite code_le_j_top_left : code_simpl.

Lemma code_le_j_top_right (Var : Set) (x : Code Var) : x || TOP == TOP.
Proof. split; auto. Qed.
Hint Rewrite code_le_j_top_right : code_simpl.

(** ** Reasoning with extensionality *)

(*
Ltac abstract M x :=
  match m with
  | x => code_ap code_i x
  | code_ap ?M1 ?M2 =>
    let code_ap N1 _ := abstract M1 x in
    let code_ap N2 _ := abstract M2 x in
    code_ap (code_ap (code_ap code_s N1) N2) x
  | _ => code_ap code_k x
  end.

Ltac beta_subs :=
  match goal with
  | beta x y
*)

Lemma code_le_extensionality (Var : Set) (x x' : Code Var) :
  (forall y, x * y [= x' * y) -> x [= x'.
Proof.
  unfold code_le; intros H Var' c f Hconv.
  (* TODO implement via abstraction algorithm *)
Admitted.

Lemma code_eq_extensionality (Var : Set) (x x' : Code Var) :
  (forall y, x * y == x' * y) -> x == x'.
Proof.
  intro H; split; apply code_le_extensionality; apply H.
Qed.

Tactic Notation "eta_expand" :=
  let x := fresh in
  match goal with
  | [|- _ [= _] => apply code_le_extensionality; intro x
  | [|- _ == _] => apply code_eq_extensionality; intro x
  end.

Tactic Notation "eta_expand" "as" ident(x) :=
  match goal with
  | [|- _ [= _] => apply code_le_extensionality; intro x
  | [|- _ == _] => apply code_eq_extensionality; intro x
  end.

Tactic Notation "eta_expand" "in" hyp(H) :=
  eapply code_le_ap_left in H; beta_reduce in H.

Ltac beta_eta :=
  beta_reduce; auto
  || eta_expand; beta_reduce; auto
  || eta_expand; eta_expand; beta_reduce; auto
  || eta_expand; eta_expand; eta_expand; beta_reduce; auto.

Lemma code_eq_ap_top (Var : Set) (x : Code Var) : TOP * x == TOP.
Proof.
  split; auto.
  (* OLD
  rewrite (pi_top (K * TOP)); beta_simpl; auto.
  *)
Admitted.
Hint Rewrite code_eq_ap_top : code_simpl.

Lemma code_eq_ap_bot (Var : Set) (x : Code Var) : BOT * x == BOT.
Proof.
  split; auto.
Admitted.
Hint Rewrite code_eq_ap_bot : code_simpl.

(** ** Reasoning about closed terms *)

(** A term is closed if it has no variables.
    In proving [x [= y], it will sometimes be easier to consider only
    closing variable assignments [f : Var -> Code Empty_set].
    Thus we introduce an equivalent definition of [x [= y]. *)

Definition code_le_empty {Var : Set} (x y : Code Var) :=
  let Var' := Empty_set in
  forall (c : Code Var') (f : Var -> Code Var'),
  conv (c * (x @ f)) -> conv (c * (y @ f)).

Lemma code_le_empty_complete (Var : Set) (x x' : Code Var) :
  x [= x' -> code_le_empty x x'.
Proof.
  unfold code_le, code_le_empty; intros; auto.
Qed.

Lemma code_le_empty_sound (Var : Set) (x x' : Code Var) :
  code_le_empty x x' -> x [= x'.
Proof.
  unfold code_le; intros H Var' c f Hconv.
Admitted.

Theorem code_le_empty_equiv (Var : Set) (x x' : Code Var) :
  x [= x' <-> code_le_empty x x'.
Proof.
  split; [apply code_le_empty_complete | apply code_le_empty_sound].
Qed.

(** ** Head-normalized versions of convergence and ordering  *)

Fixpoint code_apply {Var : Set} (x : Code Var) (ys : list (Code Var)) :
  Code Var :=
  match ys with
  | nil => x
  | (y ::ys')%list => code_apply (x * y) ys'
  end.

Notation "x ** y" := (code_apply x y) : code_scope.

Fixpoint code_repeat {Var : Set} (x : Code Var) (n : nat) : list (Code Var) :=
  match n with
  | 0 => nil
  | Succ n' => (x :: code_repeat x n')%list
  end.

Notation "x ^^ n" := (code_repeat x n) : code_scope.

Fixpoint code_tuple {Var : Set} (ys : list (Code Var)) : Code Var :=
  match ys with
  | nil => I
  | (y :: ys')%list => code_tuple ys' o (C * I * y)
  end.

Lemma beta_tuple_apply (Var : Set) (ys : list (Code Var)) :
  forall x : Code Var, beta (code_tuple ys * x) (x ** ys).
Proof.
  induction ys; simpl; auto; intro x.
  rewrite beta_b.
  rewrite beta_c.
  rewrite beta_i.
  auto.
Qed.
Hint Resolve beta_tuple_apply.

Lemma beta_apply_tuple (Var : Set) (ys : list (Code Var)) :
  forall x : Code Var, beta (x ** ys) (code_tuple ys * x).
Proof.
  induction ys; simpl; auto; intro x.
  rewrite beta_b.
  rewrite beta_c.
  rewrite beta_i.
  auto.
Qed.
Hint Resolve beta_apply_tuple.

Instance code_tuple_le (Var : Set) :
  Proper (Forall2 code_le ==> code_le) (@code_tuple Var).
Proof.
  intros xs xs' xsxs'; induction xsxs'; simpl; auto.
Qed.

Lemma code_repeat_top (Var : Set) (ys : list (Code Var)):
  Forall2 code_le ys (TOP ^^ length ys).
Proof.
  induction ys; simpl; auto.
Qed.
Hint Resolve code_repeat_top.

Lemma ap_top_conv (Var : Set) (x : Code Var) : conv x <-> conv (x * TOP).
Proof.
Admitted.

Definition code_le_apply {Var : Set} (x x' : Code Var) : Prop :=
  forall (Var' : Set) (ys : list (Code Var')) (f : Var -> Code Var'),
  conv ((x @ f) ** ys) -> conv ((x' @ f) ** ys).

Lemma code_le_apply_complete (Var : Set) (x x' : Code Var) :
  x [= x' -> code_le_apply x x'.
Proof.
  unfold code_le; intros H Var' ys f Hconv.
  rewrite beta_apply_tuple; apply H.
  rewrite beta_tuple_apply; auto.
Qed.

Lemma code_le_apply_sound (Var : Set) (x x' : Code Var) :
  code_le_apply x x' -> x [= x'.
Proof.
  unfold code_le; intros H Var' c f Hconv.
  assert (forall (ys : list (Code Var')),
    conv ((x @ f) ** ys) -> conv ((x' @ f) ** ys)) as H'; auto; clear H.
  set (y := x @ f) in *; set (y' := x' @ f) in *.
  inversion Hconv; simpl; auto.
Admitted.

Theorem code_le_apply_equiv (Var : Set) (x x' : Code Var) :
  x [= x' <-> code_le_apply x x'.
Proof.
  split; [apply code_le_apply_complete | apply code_le_apply_sound].
Qed.

Ltac code_le_apply := apply code_le_apply_equiv; unfold code_le_apply.

Lemma code_le_apply_weaken (Var : Set) (x : Code Var) (ys : list (Code Var)) :
  conv (x ** ys) -> conv x.
Proof.
  induction ys.
    simpl; auto.
  unfold code_apply; fold (@code_apply Var).
  (* TODO *)
Admitted.
