(** * Information ordering and observable equivalence *)

Require Import Coq.Logic.Classical_Prop.
Require Import Coq.Program.Basics.
Require Import Coq.Program.Equality.
Require Import Coq.Setoids.Setoid.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Lists.List.
Require Export Convergence.
Open Scope code_scope.

Definition code_le {Var : Set} (x y : Code Var) :=
  forall (Var' : Set) (c : Code Var') (f : Var -> Code Var'),
  code_conv (c * (x @ f)) -> code_conv (c * (y @ f)).
Notation "x [= y" := (code_le x y)%code : code_scope.

Definition code_eq {Var : Set} (x y : Code Var) := x [= y /\ y [= x.
Notation "x == y" := (code_eq x y)%code : code_scope.

Definition code_ple {Var : Set} (x y : Code Var) :=
  forall (Var' : Set) (c : Code Var') (f : Var -> Code Var') (p : dyadic),
  code_pconv (c * (x @ f)) p -> code_pconv (c * (y @ f)) p.

Definition code_pnle {Var : Set} (x y : Code Var) :=
  exists (Var' : Set) (c : Code Var') (f : Var -> Code Var'),
  forall (p : dyadic),
  code_pconv (c * (x @ f)) p -> code_pconv (c * (y @ f)) p.

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
  subrelation beta (@code_le Var).
Proof.
  intros x y H; apply code_le_beta; auto.
Qed.

Lemma code_eq_beta (Var : Set) (x y : Code Var) : beta x y -> x == y.
Proof.
  unfold code_le; intro H; split; intros Var' c f Hc.
  rewrite <- H; auto.
  rewrite -> H; auto.
Qed.
Hint Resolve code_eq_beta.

Instance code_eq_beta_subrelation (Var : Set) :
  subrelation beta (@code_eq Var).
Proof.
  simpl_relation; apply code_eq_beta; auto.
Qed.

Instance code_le_proper_pi (Var : Set) :
  Proper (pi ++> pi --> impl) (@code_le Var).
Proof.
  intros x x' Hx y y' Hy; unfold code_le; intros Hle Var' c f Hc.
  unfold flip in *.
  rewrite Hy.
  apply Hle; rewrite -> Hx; auto.
Qed.

Instance code_le_pi_subrelation (Var : Set) :
  subrelation (inverse pi) (@code_le Var).
Proof.
  unfold subrelation, predicate_implication, pointwise_lifting, flip.
  intros x y H; unfold code_le; intros Var' c f Hc.
  rewrite -> H; auto.
Qed.

Instance code_le_refl (Var : Set) : Reflexive (@code_le Var).
Proof.
  unfold code_le; auto.
Qed.

Instance code_eq_refl (Var : Set) : Reflexive (@code_eq Var).
Proof.
  simpl_relation.
Qed.

Instance code_le_trans (Var : Set) : Transitive (@code_le Var).
Proof.
  unfold code_le; auto.
Qed.

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
Proof.
  simpl_relation.
Qed.

Lemma code_le_ap_right (Var : Set) (x y y' : Code Var) :
  y [= y' -> x * y [= x * y'.
Proof.
  unfold code_le; intros H Var' c f.
  repeat rewrite code_sub_ap.
  intros Hconv.
  rewrite <- beta_b.
  apply H.
  rewrite -> beta_b.
  auto.
Qed.
Hint Resolve code_le_ap_right.

Lemma code_le_ap_left (Var : Set) (x x' y : Code Var) :
  x [= x' -> x * y [= x' * y.
Proof.
  unfold code_le; intros H Var' c f.
  repeat rewrite code_sub_ap.
  intros Hconv.
  rewrite <- (beta_right (beta_left beta_i)).
  rewrite <- (beta_right beta_c).
  rewrite <- beta_b.
  apply H.
  rewrite -> beta_b.
  rewrite -> (beta_right beta_c).
  rewrite -> (beta_right (beta_left beta_i)).
  auto.
Qed.
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

Instance conv_proper_le (Var : Set) : Proper (code_le ++> impl) (@code_conv Var).
Proof.
  intros x y Hxy Hc; unfold code_le in Hxy.
  rewrite <- var_monad_unit_right; rewrite <- beta_i.
  apply Hxy; code_simpl; auto.
Qed.

Instance conv_proper_eq (Var : Set) : Proper (code_eq ==> iff) (@code_conv Var).
Proof.
  intros x y [Hxy Hyx]; split; intro Hc;
  [rewrite <- Hxy | rewrite <- Hyx]; auto.
Qed.

Lemma code_sub_le_left
  (Var Var' : Set) (f g : Var -> Code Var') (x : Code Var) :
  (forall v, f v [= g v) -> x @ f [= x @ g.
Proof.
  induction x; simpl; auto.
Qed.

Lemma code_sub_le_right
  (Var Var' : Set) (f : Var -> Code Var') (x y : Code Var) :
  x [= y -> x @ f [= y @ f.
Proof.
  intros H Var'' c f'; repeat rewrite var_monad_assoc; auto.
Qed.

Instance code_sub_proper_le (Var Var' : Set) :
  Proper ((eq ==> code_le) ==> code_le ==> code_le) (@code_sub Var Var').
Proof.
  intros f g Hfg x y Hxy; transitivity (y @ f);
  [apply code_sub_le_right | apply code_sub_le_left]; auto.
Qed.

Lemma code_sub_le {Var Var' : Set} (f : Var -> Code Var') (x y : Code Var) :
  x [= y -> x @ f [= y @ f.
Proof.
  intro xy; rewrite xy; reflexivity.
Qed.

Instance code_sub_proper_eq (Var Var' : Set) :
  Proper ((eq ==> code_eq) ==> code_eq ==> code_eq) (@code_sub Var Var').
Proof.
  intros f g Hfg x y Hxy; transitivity (y @ f); split.
  - rewrite Hxy; auto.
  - rewrite <- Hxy; auto.
  - rewrite Hfg; auto.
  - rewrite <- Hfg; auto.
Qed.

Lemma code_sub_eq {Var Var' : Set} (f : Var -> Code Var') (x y : Code Var) :
  x == y -> x @ f == y @ f.
Proof.
  intro xy; rewrite xy; reflexivity.
Qed.

Lemma code_le_top (Var : Set) (x : Code Var) : x [= TOP.
Proof.
  intros; rewrite (pi_top x); auto.
Qed.
Hint Resolve code_le_top.

Lemma code_le_bot (Var : Set) (x : Code Var) : BOT [= x.
Proof.
  unfold code_le; intros Var' c f Hred.
  simpl in Hred.
  rewrite -> (pi_right (pi_bot _)).
  auto.
Qed.
Hint Resolve code_le_bot.

Lemma absolute_consistency (Var : Set) : ~ TOP [= (BOT : Code Var).
Proof.
  intro H; unfold code_le in H.
  apply (@not_conv_bot Var).
  rewrite <- beta_i; rewrite <- var_monad_unit_right.
  apply H; code_simpl; auto.
Qed.
Hint Resolve absolute_consistency.

(** ** Basic properties of information ordering *)

Lemma code_le_j_left (Var : Set) (x y : Code Var) : x [= x || y.
Proof.
  unfold code_le; intros Var' c f Hred.
  rewrite pi_j_left; auto.
Qed.
Hint Resolve code_le_j_left.

Lemma code_le_j_right (Var : Set) (x y : Code Var) : y [= x || y.
Proof.
  unfold code_le; intros Var' c f Hred.
  rewrite pi_j_right; auto.
Qed.
Hint Resolve code_le_j_right.

Lemma code_le_j_ub (Var : Set) (x y z : Code Var) :
  x [= z -> y [= z -> x || y [= z.
Proof.
  unfold code_le; intros Hx Hy Var' c f Hc.
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
Proof.
  split; auto.
Qed.
Hint Resolve code_eq_j_idem.

Lemma code_le_j_sym (Var : Set) (x y : Code Var) : x||y == y||x.
Proof.
  split; auto.
Qed.

Lemma code_eq_j_assoc (Var : Set) (x y z : Code Var) : x||(y||z) == (x||y)||z.
Proof.
  split; auto.
    apply code_le_j_ub; auto.
    transitivity (x||y); auto.
  apply code_le_j_ub; auto.
  transitivity (y||z); auto.
Qed.

Lemma code_le_j_ap_right (Var : Set) (f x y : Code Var) :
  f * x || f * y [= f * (x || y).
Proof.
  apply code_le_join; split; monotonicity.
Qed.

Lemma code_le_j_bot_left (Var : Set) (x : Code Var) : BOT || x == x.
Proof.
  split; auto.
Qed.
Hint Rewrite code_le_j_bot_left : code_simpl.

Lemma code_le_j_bot_right (Var : Set) (x : Code Var) : x || BOT == x.
Proof.
  split; auto.
Qed.
Hint Rewrite code_le_j_bot_right : code_simpl.

Lemma code_le_j_top_left (Var : Set) (x : Code Var) : TOP || x == TOP.
Proof.
  split; auto.
Qed.
Hint Rewrite code_le_j_top_left : code_simpl.

Lemma code_le_j_top_right (Var : Set) (x : Code Var) : x || TOP == TOP.
Proof.
  split; auto.
Qed.
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
  rewrite (pi_top (K * TOP : Code Var)) at 2; beta_simpl; auto.
Qed.
Hint Rewrite code_eq_ap_top : code_simpl.

Lemma code_eq_b_i (Var : Set) (x : Code Var) : I o x == x.
Proof.
  beta_eta.
Qed.
Hint Rewrite code_eq_b_i : code_simpl.

Lemma code_eq_c_b_i (Var : Set) (x : Code Var) : x o I == x.
Proof.
  beta_eta.
Qed.
Hint Rewrite code_eq_c_b_i : code_simpl.

Lemma code_eq_b_assoc (Var : Set) (f g h : Code Var) :
  (f o g) o h == f o (g o h).
Proof.
  eta_expand; beta_simpl; reflexivity.
Qed.
Hint Rewrite code_eq_b_assoc : code_simpl.

Lemma code_eq_s_k_b (Var : Set) (x : Code Var) : S * (K * x) == B * x.
Proof.
  beta_eta.
Qed.
Hint Rewrite code_eq_s_k_b : code_simpl.

Lemma code_eq_s_k_c (Var : Set) (x y : Code Var) :
  S * x * (K * y) == C * x * y.
Proof.
  beta_eta.
Qed.
Hint Rewrite code_eq_s_k_c : code_simpl.

(** We will use classical reasoning for case analysis. *)

Lemma case_le (Var : Set) (x y : Code Var) (p : Prop) :
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

Fixpoint code_apply {Var : Set} (x : Code Var) (ys : list (Code Var)) :
  Code Var :=
  match ys with
  | nil => x
  | (y ::ys')%list => code_apply (x * y) ys'
  end.

Notation "x ** y" := (code_apply x y)%code : code_scope.

Instance code_apply_proper_le (Var : Set) :
  Proper (code_le ==> eq ==> code_le) (@code_apply Var).
Proof.
  intros x x' xx' y y' yy'; subst.
  revert x x' xx'; induction y'; simpl; auto.
Qed.

Instance code_apply_proper_eq (Var : Set) :
  Proper (code_eq ==> eq ==> code_eq) (@code_apply Var).
Proof.
  intros x x' [xx' x'x] y y' yy'; subst; split;
  [rewrite xx' | rewrite x'x]; auto.
Qed.

Fixpoint code_repeat {Var : Set} (x : Code Var) (n : nat) : list (Code Var) :=
  match n with
  | 0 => nil
  | Succ n' => (x :: code_repeat x n')%list
  end.

Notation "x ^^ n" := (code_repeat x n)%code : code_scope.

Fixpoint code_tuple {Var : Set} (ys : list (Code Var)) : Code Var :=
  match ys with
  | nil => I
  | (y :: ys')%list => code_tuple ys' o (C * I * y)
  end.

Lemma beta_tuple_apply (Var : Set) (ys : list (Code Var)) :
  forall x : Code Var, beta (code_tuple ys * x) (x ** ys).
Proof.
  induction ys; simpl; auto; intro x.
  beta_simpl; auto.
Qed.
Hint Resolve beta_tuple_apply.

Instance code_tuple_le (Var : Set) :
  Proper (Forall2 code_le ==> code_le) (@code_tuple Var).
Proof.
  intros xs xs' xsxs'; induction xsxs'; simpl; auto.
Qed.

Lemma code_repeat_commute_1 (Var : Set) (x y : Code Var) (n : nat) :
  (x * y) ** y ^^ n = (x ** y ^^ n) * y.
Proof.
  revert x y; induction n; simpl; auto.
Qed.

Lemma code_repeat_top (Var : Set) (ys : list (Code Var)) :
  Forall2 code_le ys (TOP ^^ length ys).
Proof.
  induction ys; simpl; auto.
Qed.
Hint Resolve code_repeat_top.

Lemma ap_top_conv (Var : Set) (x : Code Var) : code_conv x <-> code_conv (x * TOP).
Proof.
  assert (probe x (x * TOP)) as eq; auto.
  rewrite <- eq; reflexivity.
Qed.

Definition weak_code_le {Var : Set} (x x' : Code Var) : Prop :=
  forall (ys : list (Code Empty_set)) (f : Var -> Code Empty_set),
  code_conv ((x @ f) ** ys) -> code_conv ((x' @ f) ** ys).

Lemma weak_code_le_complete (Var : Set) (x x' : Code Var) :
  x [= x' -> weak_code_le x x'.
Proof.
  unfold code_le; intros H ys f Hconv.
  rewrite <- beta_tuple_apply; apply H.
  rewrite beta_tuple_apply; auto.
Qed.

Lemma weak_code_le_sound (Var : Set) (x x' : Code Var) :
  weak_code_le x x' -> x [= x'.
Proof.
  unfold code_le; intros H Var' c f Hconv.
  assert (forall (ys : list (Code Var')),
    code_conv ((x @ f) ** ys) -> code_conv ((x' @ f) ** ys)) as H'; auto; clear H.
  set (y := x @ f) in *; set (y' := x' @ f) in *.
  inversion Hconv; simpl; auto.
  (* TODO maybe prove by induction on BT of c? *)
Admitted.

Theorem code_le_weaken (Var : Set) (x x' : Code Var) :
  x [= x' <-> weak_code_le x x'.
Proof.
  split; [apply weak_code_le_complete | apply weak_code_le_sound].
Qed.

Ltac code_le_weaken := apply code_le_weaken; unfold weak_code_le.

Lemma conv_ap (Var : Set) (x a : Code Var) : code_conv (x * a) -> code_conv x.
Proof.
  rewrite (code_le_top _ a).
  intros [y [xy yt]].
  exists y; split; auto.
  unfold close in xy; simpl in xy; fold (@close Var) in xy.
  transitivity ((close x) * TOP); auto.
Qed.

Lemma conv_apply (Var : Set) (x : Code Var) (ys : list (Code Var)) :
  code_conv (x ** ys) -> code_conv x.
Proof.
  revert x; induction ys; simpl; intros; eauto using conv_ap.
Qed.
