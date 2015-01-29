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
  intro xy; induction xy; auto.
    transitivity (y @ f); auto.
  simpl; apply probe_top; auto.
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

Lemma code_sub_test_left
  (Var Var' : Set) (f g : Var -> Code Var') (x : Code Var) :
  (forall v, test (f v) (g v)) -> test (x @ f) (x @ g).
Proof.
  intros fg; induction x; auto.
    compute; auto.
  unfold code_sub; fold (@code_sub Var Var').
  rewrite IHx1; rewrite IHx2; auto.
Qed.
Hint Resolve code_sub_test_left.

Lemma code_sub_test_right
  (Var Var' : Set) (f : Var -> Code Var') (x y : Code Var) :
  test x y -> test (x @ f) (y @ f).
Proof.
  intro xy; induction xy; repeat rewrite code_sub_ap; simpl; auto.
  transitivity (y @ f); auto.
Qed.
Hint Resolve code_sub_test_right.

Instance code_sub_proper_test (Var Var' : Set) :
  Proper ((eq ==> test) ==> test ==> test) (@code_sub Var Var').
Proof.
  intros f g Hfg x y Hxy; transitivity (y @ f);
  [apply code_sub_test_right | apply code_sub_test_left]; auto.
Qed.