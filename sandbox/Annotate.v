Require Import Omega.
Require Import Coq.Program.Basics.
Require Import Coq.Program.Equality.
Require Import Coq.Setoids.Setoid.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Logic.Decidable.
Require Import Coq.Bool.Bool.
Require Export BohmTrees.

(* for reference only:

Inductive Term {Vs : Set} : Set :=
  | term_top : Term
  | term_bot : Term
  | term_join : Term -> Term -> Term
  | term_app : Term -> Term -> Term
  | term_var : Vs -> Term
  | term_lambda : @Term (option Vs) -> Term.
Arguments Term : default implicits.
Hint Constructors Term.

Inductive normal {Vs : Set} : Term Vs -> Prop :=
  | normal_bot : normal term_bot
  | normal_join x y : normal x -> normal y -> normal (term_join x y)
  | normal_inert x : inert x -> normal x
  | normal_lambda x : @normal (option Vs) x -> normal (term_lambda x)
with inert {Vs : Set} : Term Vs -> Set :=
  | inert_var v : inert (term_var v)
  | inert_app x y : inert x -> normal y -> inert (term_app x y).
Hint Constructors normal inert.

*)

(* ------------------------------------------------------------------------ *)
(** Normal forms *)

Inductive Normal {Vs : Set} : Set :=
  | Normal_bot : Normal
  | Normal_join : Normal -> Normal -> Normal
  | Normal_rand : Normal -> Normal -> Normal
  | Normal_lambda : @Normal (option Vs) -> Normal
  | Normal_inert : Inert -> Normal
with Inert {Vs : Set} : Set :=
  | Inert_var : Vs -> Inert
  | Inert_app : Inert -> Normal -> Inert.
Hint Constructors Normal Inert.
Arguments Normal : default implicits.
Arguments Inert : default implicits.

Fixpoint eval_normal {Vs : Set} (x : Normal Vs) : Term Vs :=
  match x with
  | Normal_bot => term_bot
  | Normal_join x1 x2 => term_join (eval_normal x1) (eval_normal x2)
  | Normal_rand x1 x2 => term_rand (eval_normal x1) (eval_normal x2)
  | Normal_inert i => eval_inert i
  | Normal_lambda x1 => term_lambda (eval_normal x1)
  end
with eval_inert {Vs : Set} (x : Inert Vs) : Term Vs :=
  match x with
  | Inert_app x1 x2 => term_app (eval_inert x1) (eval_normal x2)
  | Inert_var v => term_var v
  end.

Fixpoint
  eval_normal_normal (Vs : Set) (n : Normal Vs) : normal (eval_normal n)
with
  eval_inert_inert (Vs : Set) (i : Inert Vs) : inert (eval_inert i).
Proof.
  induction n; simpl; auto.
  induction i; simpl; auto.
Qed.

(* ------------------------------------------------------------------------ *)
(** Types *)

Inductive Tp {Vs : Set} : Set :=
  | Tp_var : Vs -> Tp
  | Tp_exp : Tp -> Tp -> Tp
  | Tp_all : @Tp (option Vs) -> Tp
  (* TODO allow constants like [I] and [bool] *)
  (* TODO allow recursion via mu *)
.
Hint Constructors Tp.
Arguments Tp : default implicits.

Definition A {Vs : Set} : Term Vs. Admitted.

Section eval_type.
  Definition flip_var {Ts Vs : Set} (v : Ts + Ts + Vs) : Ts + Ts + Vs :=
    match v with
    | inl (inl v') => inl (inr v')
    | inl (inr v') => inl (inl v')
    | inr v' => inr v'
    end.

  Definition term_exp {Vs : Set} (a b : Term Vs) : Term Vs :=
    let Vs' : Set := option (option Vs) in
    let f : Term Vs' := term_var None in
    let x : Term Vs' := term_var (Some None) in
    let a' : Term Vs' := term_map (fun v => Some (Some v)) a in
    let b' : Term Vs' := term_map (fun v => Some (Some v)) b in
    term_lambda (term_lambda (b' * (f * (a' * x)))).

  Definition eval_var {Ts Vs : Set} (v : option Ts + option Ts + Vs) :
    option (option (Ts + Ts + Vs)) :=
    match v with
    | inl (inl None) => None
    | inl (inr None) => Some None
    | inl (inl (Some v')) => Some (Some (inl (inl v')))
    | inl (inr (Some v')) => Some (Some (inl (inr v')))
    | inr v' => Some (Some (inr v'))
    end.

  Definition bind_var {Vs : Set} (x : Term (option (option Vs))) : Term Vs :=
    A * LAMBDA (LAMBDA x).

  Fixpoint eval_type' {Ts Vs : Set} (a : Tp Ts) : Term (Ts + Ts + Vs) :=
    match a with
    | Tp_var v => term_var (inl (inl v))
    | Tp_exp a b =>
        let a' := eval_type' a in
        let b' := eval_type' b in
        term_exp (term_map flip_var a') b'
    | Tp_all a =>
        let a' := eval_type' a in
        bind_var (term_map eval_var a')
    end.

  Definition close_type {Vs : Set} :
    Term (Empty_set + Empty_set + Vs) -> Term Vs :=
    term_map (fun v =>
    match v with
    | inr v' => v'
    | inl (inr v') => match v' : Empty_set with end
    | inl (inl v') => match v' : Empty_set with end
    end).

  Definition eval_type {Vs : Set} (a : Tp Empty_set) : Term Vs :=
    close_type (eval_type' a).
End eval_type.

(* ------------------------------------------------------------------------ *)
(** Annotated normal forms *)

Inductive TNormal {Ts Vs : Set} : Set :=
  | TNormal_bot : TNormal
  | TNormal_join : TNormal -> TNormal -> TNormal
  | TNormal_rand : TNormal -> TNormal -> TNormal
  | TNormal_inert : TInert -> TNormal
  | TNormal_lambda : @TNormal Ts (option Vs) -> TNormal
  | TNormal_ann : Tp Ts -> TNormal -> TNormal
with TInert {Ts Vs : Set} : Set :=
  | TInert_var : Vs -> TInert
  | TInert_app : TInert -> TNormal -> TInert
  | TInert_ann : Tp Ts -> TInert -> TInert.
Hint Constructors TNormal TInert.
Arguments TNormal : default implicits.
Arguments TInert : default implicits.

Fixpoint eval_tnormal {Vs : Set} (x : TNormal Empty_set Vs) : Term Vs :=
  match x with
  | TNormal_bot => term_bot
  | TNormal_join x1 x2 => term_join (eval_tnormal x1) (eval_tnormal x2)
  | TNormal_rand x1 x2 => term_rand (eval_tnormal x1) (eval_tnormal x2)
  | TNormal_inert i => eval_tinert i
  | TNormal_lambda x1 => term_lambda (eval_tnormal x1)
  | TNormal_ann a x1 => term_app (eval_type a) (eval_tnormal x1)
  end
with eval_tinert {Vs : Set} (x : TInert Empty_set Vs) : Term Vs :=
  match x with
  | TInert_app x1 x2 => term_app (eval_tinert x1) (eval_tnormal x2)
  | TInert_var v => term_var v
  | TInert_ann a1 x1 => term_app (eval_type a1) (eval_tinert x1)
  end.

Fixpoint tnormal_map {Vs Vs' Ts : Set} (f : Vs -> Vs') (x : TNormal Ts Vs) :
  TNormal Ts Vs' :=
  match x with
  | TNormal_bot => TNormal_bot
  | TNormal_join x1 x2 => TNormal_join (tnormal_map f x1) (tnormal_map f x2)
  | TNormal_rand x1 x2 => TNormal_rand (tnormal_map f x1) (tnormal_map f x2)
  | TNormal_inert i => TNormal_inert (tinert_map f i)
  | TNormal_lambda x1 => TNormal_lambda (tnormal_map (option_map f) x1)
  | TNormal_ann a x1 => TNormal_ann a (tnormal_map f x1)
  end
with tinert_map {Ts Vs Vs' : Set}  (f : Vs -> Vs') (x : TInert Ts Vs) :
  TInert Ts Vs' :=
  match x with
  | TInert_app x1 x2 => TInert_app (tinert_map f x1) (tnormal_map f x2)
  | TInert_var v => TInert_var (f v)
  | TInert_ann a1 x1 => TInert_ann a1 (tinert_map f x1)
  end.

Definition tnormal_some_sub
  {Ts Vs Vs' : Set} (f : Vs -> TInert Ts Vs') (v : option Vs) :
  TInert Ts (option Vs') :=
  match v with
  | None => TInert_var None
  | Some v' => tinert_map (@Some Vs') (f v')
  end.

Fixpoint
  tnormal_sub {Ts Vs Vs' : Set} (f : Vs -> TInert Ts Vs') (x : TNormal Ts Vs) :
  TNormal Ts Vs' :=
  match x with
  | TNormal_bot => TNormal_bot
  | TNormal_join x1 x2 => TNormal_join (tnormal_sub f x1) (tnormal_sub f x2)
  | TNormal_rand x1 x2 => TNormal_rand (tnormal_sub f x1) (tnormal_sub f x2)
  | TNormal_inert i => TNormal_inert (tinert_sub f i)
  | TNormal_lambda x1 => TNormal_lambda (tnormal_sub (tnormal_some_sub f) x1)
  | TNormal_ann a x1 => TNormal_ann a (tnormal_sub f x1)
  end
with
  tinert_sub {Ts Vs Vs' : Set}  (f : Vs -> TInert Ts Vs') (x : TInert Ts Vs) :
  TInert Ts Vs' :=
  match x with
  | TInert_app x1 x2 => TInert_app (tinert_sub f x1) (tnormal_sub f x2)
  | TInert_var v => f v
  | TInert_ann a1 x1 => TInert_ann a1 (tinert_sub f x1)
  end.

(* ------------------------------------------------------------------------ *)
(** Type checking *)

Definition ann_lambda {Ts Vs : Set} (a : Tp Ts) :
  TNormal Ts (option Vs) -> TNormal Ts (option Vs) :=
  tnormal_sub (
    fun v =>
    match v with
    | None => TInert_ann a (TInert_var None)
    | Some v => TInert_var (Some v)
    end).

Definition ann_lambda' {Ts Vs : Set} (a : Tp Ts) :
  TInert Ts (option Vs) -> TInert Ts (option Vs) :=
  tinert_sub (
    fun v =>
    match v with
    | None => TInert_ann a (TInert_var None)
    | Some v => TInert_var (Some v)
    end).

Inductive checks {Ts Vs : Set} : relation (TNormal Ts Vs) :=
  | checks_refl x : checks x x
  | checks_trans x y z : checks x y -> checks y z -> checks x z
  | checks_bot x : checks x TNormal_bot
  | checks_join_left x y : checks (TNormal_join x y) x
  | checks_join_right x y : checks (TNormal_join x y) y
  (* ...app etc... *)
  | checks_expand_lambda a b x :
      checks (TNormal_ann (Tp_exp a b) (TNormal_lambda x))
             (TNormal_lambda (TNormal_ann b (ann_lambda a x)))
  | checks_expand_join a x y :
      checks (TNormal_ann a (TNormal_join x y))
             (TNormal_join (TNormal_ann a x) (TNormal_ann a y))
  | checks_expand_rand a x y :
      checks (TNormal_ann a (TNormal_rand x y))
             (TNormal_rand (TNormal_ann a x) (TNormal_ann a y))
  | checks_eta_expand x :
      checks x (TNormal_lambda (tnormal_map (@Some Vs) x))
  (* TODO
  (* How to deal with covariance vs contravariance? *)
  | checks_conjugate :
  | checks_identity :
  | checks_clash_var_var :
  | checks_clash_var_exp :
  | checks_clash_exp_var :
  *)
with checks' {Ts Vs : Set} : relation (TInert Ts Vs) :=
  (* TODO *)
.

Instance checks_sound (Vs : Set) :
  Proper (checks --> term_le) (@eval_tnormal Vs).
Proof.
  intros y x xy; induction xy; simpl; try (term_to_code; auto; reflexivity).
  - transitivity (eval_tnormal y); auto.
  - admit. (* TODO define [eval_type] *)
  - admit.
    (* TODO show [eval_type a (x (+) y) [= eval_type a x (+) eval_type a y]. *)
  - admit.
Qed.

Fixpoint check_step {Ts Vs : Set} (x : TNormal Ts Vs) :
  option (TNormal Ts Vs) :=
  match x with
  (* TODO
  | TNormal_bot => term_bot
  | TNormal_join x1 x2 => term_join (eval_tnormal x1) (eval_tnormal x2)
  | TNormal_rand x1 x2 => term_rand (eval_tnormal x1) (eval_tnormal x2)
  | TNormal_inert i => eval_tinert i
  | TNormal_lambda x1 => term_lambda (eval_tnormal x1)
  | TNormal_ann a x1 => term_app (eval_type a) (eval_tnormal x1)
  *)
  | _ => None
  end
with check_step' {Ts Vs : Set} (x : TInert Ts Vs) :
  option (TInert Ts Vs) :=
  match x with
  (* TODO
  | TInert_app x1 x2 => term_app (eval_tinert x1) (eval_tnormal x2)
  | TInert_var v => term_var v
  | TInert_ann a1 x1 => term_app (eval_type a1) (eval_tinert x1)
  *)
  | _ => None
  end.

Fixpoint check_step_checks (Ts Vs : Set) (x : TNormal Ts Vs) :
  match check_step x with
  | None => True
  | Some y => checks x y
  end
with check_step_checks' (Ts Vs : Set) (x : TInert Ts Vs) :
  match check_step' x with
  | None => True
  | Some y => checks' x y
  end.
Proof.
  - admit.
  - admit.
Admitted.

Fixpoint try_check {Ts Vs : Set} (n : nat) (x : TNormal Ts Vs) :
  option bool :=
  match n with
  | 0%nat => None
  | Datatypes.S n' =>
    match check_step x with
    | Some x' => try_check n' x'
    | None => (* TODO *) Some false
    end
  end.

(* TODO
Instance checks_complete (Ts Vs : Set) (x y : TNormal Ts Vs) : ???
*)

(* FIXME
Definition fixes {Ts Vs : Set} (a : Tp Ts) (x : TNormal Ts Vs) : Prop :=
  checks (TNormal_ann a x) x.
*)
