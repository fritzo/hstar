(** * Substitution *)

Require Import Coq.Program.Equality.
Require Import Coq.Setoids.Setoid.
Require Import Coq.Classes.Morphisms.
Require Export Terms.

(* adapted from https://coq.inria.fr/cocorico/UntypedLambdaTerms *)

Lemma ext_respectful
  (a b : Type) (f g : a -> b) (r : relation b) (fg : forall x, r (f x) (g x)) :
  respectful eq r f g.
Proof.
  intros x x' xx'; rewrite xx'; auto.
Qed.

Instance option_map_proper (Var Var' : Set) :
  Proper ((eq ==> eq) ==> eq ==> eq) (@option_map Var Var').
Proof.
  intros f f' ff' v v' vv'; compute in ff'; rewrite <- vv'; clear v' vv'.
  case_eq v; intros; simpl; auto.
  rewrite (ff' v0 v0); auto.
Qed.

Fixpoint term_map {Var Var' : Set} (f : Var -> Var') (x : Term Var) :
  Term Var' :=
  match x with
  | TOP => TOP
  | BOT => BOT
  | x1 || x2 => term_map f x1 || term_map f x2
  | x1 (+) x2 => term_map f x1 (+) term_map f x2
  | x1 * x2 => term_map f x1 * term_map f x2
  | VAR x => VAR (f x)
  | LAMBDA x1 => LAMBDA (term_map (option_map f) x1)
  end.

Instance term_map_proper (Var Var' : Set) :
  Proper ((eq ==> eq) ==> eq ==> eq) (@term_map Var Var').
Proof.
  intros f f' ff' x x' xx'; compute in ff'; rewrite <- xx'; clear x' xx'.
  revert Var' f f' ff'; induction x; intros Var' f f' ff'; simpl; auto.
  - rewrite (IHx1 Var' f f'), (IHx2 Var' f f'); auto.
  - rewrite (IHx1 Var' f f'), (IHx2 Var' f f'); auto.
  - rewrite (IHx1 Var' f f'), (IHx2 Var' f f'); auto.
  - rewrite (ff' v v); auto.
  - rewrite (IHx (option Var') (option_map f) (option_map f')); auto.
    apply option_map_proper; auto.
Qed.

Definition some_sub
  {Var Var' : Set} (f : Var -> Term Var') (v : option Var) :
  Term (option Var') :=
  match v with
  | None => VAR None
  | Some v' => term_map (@Some Var') (f v')
  end.

Instance some_sub_proper (Var Var' : Set) :
  Proper ((eq ==> eq) ==> eq ==> eq) (@some_sub Var Var').
Proof.
  intros f f' ff' v v' vv'; compute in ff'; rewrite <- vv'; clear v' vv'.
  case_eq v; intros; simpl; auto.
  rewrite (ff' v0 v0); auto.
Qed.

Fixpoint term_sub {Var Var' : Set} (f : Var -> Term Var') (x : Term Var) :
  Term Var' :=
  match x with
  | TOP => TOP
  | BOT => BOT
  | x1 || x2 => term_sub f x1 || term_sub f x2
  | x1 (+) x2 => term_sub f x1 (+) term_sub f x2
  | x1 * x2 => term_sub f x1 * term_sub f x2
  | VAR v => f v
  | LAMBDA x1 => LAMBDA (term_sub (some_sub f) x1)
  end.

Instance term_sub_proper (Var Var' : Set) :
  Proper ((eq ==> eq) ==> eq ==> eq) (@term_sub Var Var').
Proof.
  intros f f' ff'; compute in ff'.
  intros x x' xx'; rewrite <- xx'; clear x' xx'.
  revert Var' f f' ff'; induction x; intros Var' f f' ff'; auto.
  - simpl; rewrite (IHx1 Var' f f'), (IHx2 Var' f f'); auto.
  - simpl; rewrite (IHx1 Var' f f'), (IHx2 Var' f f'); auto.
  - simpl; rewrite (IHx1 Var' f f'), (IHx2 Var' f f'); auto.
  - compute; auto.
  - simpl; rewrite (IHx _ (some_sub f) (some_sub f')); clear IHx; auto.
    intros v v' vv'; rewrite <- vv'; clear v' vv' x.
    apply some_sub_proper; auto.
Qed.

Notation "x @ f" := (term_sub f x) : term_scope.

Definition sub_top {Var : Set} (v : Var) : Closed := TOP.
Definition close {Var : Set} : Term Var -> Closed := term_sub sub_top.

Definition sub_empty {Var : Set} (v : Empty_set) : Var := match v with end.
Definition open (Var : Set) : Closed -> Term Var := term_map sub_empty.

Tactic Notation "term_simpl" := autorewrite with term_simpl.
Tactic Notation "term_simpl" "in" hyp(H) := autorewrite with term_simpl in H.

Lemma var_monad_unit_right (Var : Set) (x : Term Var) : x @ VAR = x.
Proof.
  induction x; auto; simpl;
  repeat
    match goal with
    | [H : _ @ VAR = _ |- _] => rewrite H; clear H
    end;
  try reflexivity.
  admit.
Qed.
Hint Rewrite var_monad_unit_right : term_simpl.

Lemma var_monad_unit_left (Var Var' : Set) (f : Var -> Term Var') x :
  (VAR x) @ f = f x.
Proof.
  compute; auto.
Qed.
Hint Rewrite var_monad_unit_left : term_simpl.

Lemma term_sub_ap (Var Var' : Set) (x y : Term Var) (f : Var -> Term Var') :
  (x * y @ f) = (x @ f) * (y @ f).
Proof.
  simpl; auto.
Qed.
Hint Rewrite term_sub_ap : term_simpl.

Lemma term_sub_join (Var Var' : Set) (x y : Term Var) (f : Var -> Term Var') :
  (x || y @ f) = (x @ f) || (y @ f).
Proof.
  simpl; auto.
Qed.
Hint Rewrite term_sub_join : term_simpl.

Lemma term_sub_rand (Var Var' : Set) (x y : Term Var) (f : Var -> Term Var') :
  (x (+) y @ f) = (x @ f) (+) (y @ f).
Proof.
  simpl; auto.
Qed.
Hint Rewrite term_sub_rand : term_simpl.

Lemma term_sub_lambda
  (Var Var' : Set) (x : Term (option Var)) (f : Var -> Term Var') :
  (LAMBDA x @ f) = LAMBDA (x @ some_sub f).
Proof.
  simpl; auto.
Qed.
Hint Rewrite term_sub_lambda : term_simpl.

Lemma var_monad_assoc
  (Var Var' Var'' : Set)
  (f : Var -> Term Var')
  (g : Var' -> Term Var'')
  (x : Term Var) :
  (x @ f) @ g = x @ (fun v => (f v) @ g).
Proof.
  revert Var' Var'' f g; induction x; intros Var' Var'' f g; auto.
  - term_simpl; rewrite IHx1; rewrite IHx2; auto.
  - term_simpl; rewrite IHx1; rewrite IHx2; auto.
  - term_simpl; rewrite IHx1; rewrite IHx2; auto.
  - term_simpl; rewrite IHx; simpl; auto.
    admit.
Qed.
Hint Rewrite var_monad_assoc : term_simpl.

Lemma close_idempotent (Var : Set) (x : Term Var) : close (close x) = close x.
Proof.
  compute; term_simpl; induction x; auto.
Qed.
Hint Rewrite close_idempotent : beta_simpl.
Hint Rewrite close_idempotent : term_simpl.

Lemma close_closed (x : Closed) : close x = x.
Proof.
  unfold Closed in x; unfold close, sub_top.
  dependent induction x; term_simpl;
  match goal with [v : Empty_set |- _] => destruct v | _ => idtac end; auto.
  - rewrite IHx1; rewrite IHx2; reflexivity.
  - rewrite IHx1; rewrite IHx2; reflexivity.
  - rewrite IHx1; rewrite IHx2; reflexivity.
  - clear IHx.
    set (f := fun _ : Empty_set => TOP).
    rewrite <- var_monad_unit_right; simpl.
    assert (forall v, f v = VAR v) as eq; [intro v; case v|].
    apply ext_respectful in eq.
    apply some_sub_proper in eq.
    apply term_sub_proper in eq.
    unfold respectful in eq.
    rewrite (eq x x); auto.
Qed.
Hint Rewrite close_closed : beta_simpl.
Hint Rewrite close_closed : term_simpl.

Lemma open_close
  (Var : Set) (f : Var -> Term Empty_set) (x : Term Empty_set) :
  (open Var x) @ f = x.
Proof.
  unfold open.
  revert Var f; dependent induction x; intros Var f; simpl; auto.
  - rewrite (IHx1 Var f), (IHx2 Var f); auto.
  - rewrite (IHx1 Var f), (IHx2 Var f); auto.
  - rewrite (IHx1 Var f), (IHx2 Var f); auto.
  - case v.
  - admit.
Qed.

Lemma term_sub_ext (Var Var' : Set)
  (f g : Var -> Term Var') (fg : forall v, f v = g v) x :
  x @ f = x @ g.
Proof.
  revert Var' f g fg; induction x; intros Var' f g fg; simpl; auto.
  - rewrite (IHx1 Var' f g), (IHx2 Var' f g); auto.
  - rewrite (IHx1 Var' f g), (IHx2 Var' f g); auto.
  - rewrite (IHx1 Var' f g), (IHx2 Var' f g); auto.
  - rewrite (IHx (option Var') (some_sub f) (some_sub g)); auto.
    apply ext_respectful in fg.
    intros; apply (some_sub_proper Var _ f g fg); auto.
Qed.
