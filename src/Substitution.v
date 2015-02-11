(** * Substitution *)

Require Import Coq.Program.Equality.
Require Import Coq.Setoids.Setoid.
Require Import Coq.Classes.Morphisms.
Require Export Terms.

(* adapted from https://coq.inria.fr/cocorico/UntypedLambdaTerms *)

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

Fixpoint term_sub {Var Var' : Set} (f : Var -> Term Var') (x : Term Var) :
  Term Var' :=
  match x with
  | TOP => TOP
  | BOT => BOT
  | x1 || x2 => term_sub f x1 || term_sub f x2
  | x1 (+) x2 => term_sub f x1 (+) term_sub f x2
  | x1 * x2 => term_sub f x1 * term_sub f x2
  | VAR v => f v
  | LAMBDA x1 => LAMBDA (term_sub (fun x => 
    match x with
    | None => VAR None
    | Some y => term_map (@Some Var') (f y)
    end) x1)
  end.

Instance term_sub_proper (Var Var' : Set) :
  Proper ((eq ==> eq) ==> eq ==> eq) (@term_sub Var Var').
Proof.
  intros f f' ff'; compute in ff'.
  intros x x' xx'; rewrite <- xx'; clear x' xx'.
  induction x; auto.
  - simpl; rewrite (IHx1 f f'), (IHx2 f f'); auto.
  - simpl; rewrite (IHx1 f f'), (IHx2 f f'); auto.
  - simpl; rewrite (IHx1 f f'), (IHx2 f f'); auto.
  - compute; auto.
  - admit.
    (* TODO how to do heterogeneous induction? *)
Qed.

Notation "x @ f" := (term_sub f x) : term_scope.

Definition sub_top {Var : Set} (v : Var) : Closed := TOP.
Definition close {Var : Set} : Term Var -> Closed := term_sub sub_top.

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

Definition lambda_map
  {Var Var' : Set} (f : Var -> Term Var') (v : option Var) :
  Term (option Var') :=
  match v with
  | None => VAR None
  | Some v' => term_map (@Some Var') (f v')
  end.

Lemma term_sub_lambda
  (Var Var' : Set) (x : Term (option Var)) (f : Var -> Term Var') :
  (LAMBDA x @ f) = LAMBDA (x @ lambda_map f).
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
  induction x; auto.
  - term_simpl; rewrite IHx1; rewrite IHx2; auto.
  - term_simpl; rewrite IHx1; rewrite IHx2; auto.
  - term_simpl; rewrite IHx1; rewrite IHx2; auto.
  - term_simpl. (* rewrite IHx; auto. *)
    admit.
    (* TODO how to do heterogeneous induction? *)
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
    set (f := lambda_map (fun _ : Empty_set => TOP)).
    assert (x @ f = x) as Eq1; [| rewrite Eq1; reflexivity].
    admit.
    (* TODO prove a stronger lemma that implies this lemma *)
Qed.
Hint Rewrite close_closed : beta_simpl.
Hint Rewrite close_closed : term_simpl.
