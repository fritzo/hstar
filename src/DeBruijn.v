(** * Lambda calculus parametric de Bruijn terms *)

(**
  We use the parametric de Bruijn convention of
  https://coq.inria.fr/cocorico/UntypedLambdaTerms
  and earlier Bird and Patterson \cite{bird1999bruijn}.
  See also Capretta and Felty \cite{capretta2007combining}.
*)

Definition Succ := S%nat.  (* an alias for later *)

Require Import Coq.Program.Basics.
Require Import Coq.Program.Equality.
Require Import Coq.Setoids.Setoid.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Export Notations.


(* ------------------------------------------------------------------------ *)
(** ** Terms *)

Inductive Term {Var : Set} : Set :=
  | term_top : Term
  | term_bot : Term
  | term_join : Term -> Term -> Term
  | term_rand : Term -> Term -> Term
  | term_app : Term -> Term -> Term
  | term_var : Var -> Term
  | term_lambda : @Term (option Var) -> Term.
Arguments Term : default implicits.
Hint Constructors Term.
Definition ClosedTerm := Term Empty_set.

Notation "'TOP'" := term_top : term_scope.
Notation "'BOT'" := term_bot : term_scope.
Notation "'JOIN'" := term_join : term_scope.
Notation "'RAND'" := term_rand : term_scope.
Notation "'APP'" := term_app : term_scope.
Notation "'VAR'" := term_var : term_scope.
Notation "'LAMBDA'" := term_lambda : term_scope.

Open Scope term_scope.
Delimit Scope term_scope with term.
Bind Scope term_scope with Term.

Notation "x * y" := (APP x y)%term : term_scope.
Notation "x || y" := (JOIN x y)%term : term_scope.
Notation "x (+) y" := (RAND x y)%term : term_scope.


(* ------------------------------------------------------------------------ *)
(** ** Lambda notation *)

Fixpoint iter {a : Type} (z : a) (s : a -> a) (n : nat) {struct n} :=
  match n with
  | 0 => z
  | Succ n' => s (iter z s n')
  end.

Fixpoint iter_dep
  {tz : Set} {ts : Set -> Set}
  (x : tz) (f : forall t : Set, t -> ts t) (n : nat) {struct n} :=
  match n return iter tz ts n with
  | 0 => x
  | Succ n' => f _ (iter_dep x f n')
  end.

Fixpoint iter_depT
  {tz : Type} {ts : Type -> Type}
  (x : tz) (f : forall t : Type, t -> ts t) (n : nat) {struct n} :=
  match n return iter tz ts n with
  | 0 => x
  | Succ n' => f _ (iter_depT x f n')
  end.

(* restrict [option] to [Set] level *)
Definition option' (a : Set) : Set := option a.
Definition Some' (a : Set) (x : a) : option' a := Some x.
Definition None' {a : Set} : option' a := None.

Definition option_ (n : nat) (v : Set) := iter v option' n.
Definition Some_ (n : nat) (v : Set) := iter_depT v Some n.
Definition lam_ {Var : Set} (n : nat) (x : Term (option_ n Var)) :=
  iter_dep x (@term_var) n.
(*
Definition var_ {Var : Set} (n : nat) : Term (option_ n Var) :=
  @VAR (option_ n Var) (iter_dep (@None' Var) Some' n).
*)

Section I.
  Definition v0 {Var : Set} : Term (option_ 1 Var) := VAR None.
  Definition v1 {Var : Set} : Term (option_ 2 Var) := VAR (Some None).
  Definition v2 {Var : Set} : Term (option_ 3 Var) := VAR (Some (Some None)).
  Context {Var : Set}.

  Definition I : Term Var := Eval compute in
    LAMBDA v0.
  Definition K : Term Var := Eval compute in
    LAMBDA (LAMBDA (VAR (Some None))).
  Definition F : Term Var := Eval compute in
    LAMBDA (LAMBDA (VAR None)).
  Definition B : Term Var := Eval compute in
    LAMBDA (LAMBDA (LAMBDA (v2 * (v1 * v0)))).
  Definition C : Term Var := Eval compute in
    LAMBDA (LAMBDA (LAMBDA (v2 * v0 * v1))).
  Definition S : Term Var := Eval compute in
    LAMBDA (LAMBDA (LAMBDA (v2 * v0 * (v1 * v0)))).
End I.
Print S.  (* Ugly! *)

Notation "x 'o' y" := (B * x * y)%term : term_scope.

(* TODO figure out how to use lambda notation
Notation "\ x , y" := (LAMBDA)%term : code_scope.
*)


(* ------------------------------------------------------------------------ *)
(** ** Substitution *)

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
  case_eq v; intro v0; intros; simpl; auto.
  assert (f v0 = f' v0) as eq; [apply ff' | rewrite eq]; auto.
Qed.

Fixpoint term_map {Var Var' : Set} (f : Var -> Var') (x : Term Var) :
  Term Var' :=
  match x with
  | TOP => TOP
  | BOT => BOT
  | x1 || x2 => term_map f x1 || term_map f x2
  | x1 (+) x2 => term_map f x1 (+) term_map f x2
  | x1 * x2 => term_map f x1 * term_map f x2
  | term_var x => VAR (f x)
  | term_lambda x1 => LAMBDA (term_map (option_map f) x1)
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
  case_eq v; intro v0; intros; simpl; auto.
  assert (f v0 = f' v0) as eq; [apply ff' | rewrite eq]; auto.
Qed.

Fixpoint term_sub {Var Var' : Set} (f : Var -> Term Var') (x : Term Var) :
  Term Var' :=
  match x with
  | TOP => TOP
  | BOT => BOT
  | x1 || x2 => term_sub f x1 || term_sub f x2
  | x1 (+) x2 => term_sub f x1 (+) term_sub f x2
  | x1 * x2 => term_sub f x1 * term_sub f x2
  | term_var v => f v
  | term_lambda x1 => LAMBDA (term_sub (some_sub f) x1)
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

Notation "x @ f" := (term_sub f x)%term : term_scope.

Definition sub_top {Var : Set} (v : Var) : ClosedTerm := TOP.
Definition close {Var : Set} : Term Var -> ClosedTerm := term_sub sub_top.

Definition sub_empty {Var : Set} (v : Empty_set) : Var := match v with end.
Definition open (Var : Set) : ClosedTerm -> Term Var := term_map sub_empty.

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

Lemma close_closed (x : ClosedTerm) : close x = x.
Proof.
  unfold ClosedTerm in x; unfold close, sub_top.
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

Definition none_sub {Var : Set} (x : Term Var) (v : option Var) : Term Var :=
  match v with
  | None => x
  | Some v' => VAR v'
  end.

Definition lambda_app_sub {Var : Set} (x : Term (option Var)) (y : Term Var) :
  Term Var := x @ (none_sub y).

Lemma lambda_app_sub_sub
  (Var : Set) (y : Term Var) (x : Term (option Var))
  (Var' : Set) (f : Var -> Term Var') :
  lambda_app_sub x y @ f = lambda_app_sub (x @ some_sub f) (y @ f).
Proof.
  revert Var' f.
  dependent induction x; intros; try (simpl; auto; reflexivity).
Admitted.
