(** * Substitution *)

Require Import Coq.Classes.Morphisms.
Require Export Codes.

Fixpoint code_sub {Var Var' : Set}
  (f : Var -> Code Var') (x : Code Var) : Code Var' :=
  match x with
  | code_var v => f v
  | l * r => (code_sub f l) * (code_sub f r)
  | TOP => TOP
  | BOT => BOT
  | J => J
  | R => R
  | I => I
  | K => K
  | B => B
  | C => C
  | S => S
  end.

Notation "x @ f" := (code_sub f x) : code_scope.

Definition sub_top {Var : Set} (v : Var) : Code Empty_set := TOP.
Definition close {Var : Set} : Code Var -> Code Empty_set := code_sub sub_top.

Lemma var_monad_unit_right (Var : Set) (x : Code Var) : x @ code_var = x.
Proof.
  induction x; auto.
  unfold code_sub; fold (@code_sub Var Var).
  rewrite IHx1; rewrite IHx2; auto.
Qed.
Hint Rewrite var_monad_unit_right : code_simpl.

Lemma var_monad_unit_left (Var Var' : Set) (f : Var -> Code Var') x :
  (code_var x) @ f = f x.
Proof.
  compute; auto.
Qed.
Hint Rewrite var_monad_unit_left : code_simpl.

Lemma code_sub_ap (Var Var' : Set)
  (x y : Code Var) (f : Var -> Code Var') : (x * y @ f) = (x @ f) * (y @ f).
Proof.
  simpl; auto.
Qed.
Hint Rewrite code_sub_ap : code_simpl.

Lemma var_monad_assoc
  (Var Var' Var'' : Set)
  (f : Var -> Code Var')
  (g : Var' -> Code Var'')
  (x : Code Var) :
  (x @ f) @ g = x @ (fun v => (f v) @ g).
Proof.
  induction x; auto.
  repeat rewrite code_sub_ap.
  rewrite IHx1; rewrite IHx2; auto.
Qed.
Hint Rewrite var_monad_assoc : code_simpl.

Lemma close_idempotent (Var : Set) (x : Code Var) :
  close (close x) = close x.
Proof.
  compute; code_simpl; induction x; auto.
Qed.
Hint Rewrite close_idempotent : beta_simpl.
Hint Rewrite close_idempotent : code_simpl.

Lemma code_sub_inverse
  (Var : Set) (f : Var -> Code Empty_set) (x : Code Empty_set) :
  exists y, y @ f = x.
Proof.
  induction x;
  match goal with
  | [v : Empty_set |- _] => case v
  | [|- exists y : Code Var, _ = ?x Empty_set] => exists (@x Var); auto
  | _ =>
    destruct IHx1 as [y1 Hy1];
    destruct IHx2 as [y2 Hy2];
    exists (y1 * y2); code_simpl; subst; auto
  end.
Qed.

Lemma code_sub_ext (Var Var' : Set)
  (f g : Var -> Code Var') (fg : forall v, f v = g v) x :
  x @ f = x @ g.
Proof.
  induction x; simpl; auto.
  rewrite IHx1; rewrite IHx2; auto.
Qed.

Lemma code_sub_proper_probe (Var Var' : Set)
  (f : Var -> Code Var') (x y : Code Var) :
  probe x y -> probe (x @ f) (y @ f).
Proof.
  intro xy; induction xy; simpl.
  - reflexivity.
  - transitivity (y @ f); auto.
  - apply probe_top; auto.
Qed.

Lemma code_sub_beta_left
  (Var Var' : Set) (f g : Var -> Code Var') (x : Code Var) :
  (forall v, beta (f v) (g v)) -> beta (x @ f) (x @ g).
Proof.
  intros fg; induction x; auto.
    compute; auto.
  unfold code_sub; fold (@code_sub Var Var').
  transitivity ((x1 @ g) * (x2 @ f)); auto.
Qed.
Hint Resolve code_sub_beta_left.

Lemma code_sub_beta_right
  (Var Var' : Set) (f : Var -> Code Var') (x y : Code Var) :
  beta x y -> beta (x @ f) (y @ f).
Proof.
  intro xy; induction xy; repeat rewrite code_sub_ap; simpl; auto.
  transitivity (y @ f); auto.
Qed.
Hint Resolve code_sub_beta_right.

Instance code_sub_proper_beta (Var Var' : Set) :
  Proper ((eq ==> beta) ==> beta ==> beta) (@code_sub Var Var').
Proof.
  intros f g Hfg x y Hxy; transitivity (y @ f);
  [apply code_sub_beta_right | apply code_sub_beta_left]; auto.
Qed.

Lemma code_sub_pi_left
  (Var Var' : Set) (f g : Var -> Code Var') (x : Code Var) :
  (forall v, pi (f v) (g v)) -> pi (x @ f) (x @ g).
Proof.
  intros fg; induction x; auto.
    compute; auto.
  unfold code_sub; fold (@code_sub Var Var').
  rewrite IHx1; rewrite IHx2; auto.
Qed.
Hint Resolve code_sub_pi_left.

Lemma code_sub_pi_right
  (Var Var' : Set) (f : Var -> Code Var') (x y : Code Var) :
  pi x y -> pi (x @ f) (y @ f).
Proof.
  intro xy; induction xy; repeat rewrite code_sub_ap; simpl; auto.
  transitivity (y @ f); auto.
Qed.
Hint Resolve code_sub_pi_right.

Instance code_sub_proper_pi (Var Var' : Set) :
  Proper ((eq ==> pi) ==> pi ==> pi) (@code_sub Var Var').
Proof.
  intros f g Hfg x y Hxy; transitivity (y @ f);
  [apply code_sub_pi_right | apply code_sub_pi_left]; auto.
Qed.

Instance code_close_proper_beta (Var : Set) :
  Proper (beta ==> beta) (@close Var).
Proof.
  intros x x' xx'; apply weaken_beta in xx'; induction xx'; auto.
  revert z xx' IHxx'; induction H; compute; code_simpl; eauto.
Qed.

Instance code_close_proper_pi (Var : Set) :
  Proper (pi ==> pi) (@close Var).
Proof.
  intros x x' xx'; apply weaken_pi in xx'; induction xx'; auto.
  revert z xx' IHxx'; induction H; compute; code_simpl; eauto.
Qed.

Lemma probe_step_close (Var : Set) (x y : Code Var) :
  probe_step x y -> probe (close x) (close y).
Proof.
  intro Hb; induction Hb; compute; auto.
Qed.

Lemma probe_close (Var : Set) (x y : Code Var) :
  probe x y -> probe (close x) (close y).
Proof.
  intro Hb; rewrite weaken_probe in Hb; induction Hb; auto.
  rewrite <- IHHb; clear Hb IHHb; auto using probe_step_close.
Qed.

Lemma beta_step_close (Var : Set) (x y : Code Var) :
  beta_step x y -> beta (close x) (close y).
Proof.
  intro Hb; induction Hb; compute; beta_reduce; auto.
Qed.

Lemma beta_close (Var : Set) (x y : Code Var) :
  beta x y -> beta (close x) (close y).
Proof.
  intro Hb; rewrite weaken_beta in Hb; induction Hb; auto.
  rewrite <- IHHb; clear Hb IHHb; auto using beta_step_close.
Qed.

Lemma pi_step_close (Var : Set) (x y : Code Var) :
  pi_step x y -> pi (close x) (close y).
Proof.
  intro Hb; induction Hb; compute; beta_reduce; auto.
Qed.

Lemma pi_close (Var : Set) (x y : Code Var) :
  pi x y -> pi (close x) (close y).
Proof.
  intro Hb; rewrite weaken_pi in Hb; induction Hb; auto.
  rewrite <- IHHb; clear Hb IHHb; auto using pi_step_close.
Qed.
