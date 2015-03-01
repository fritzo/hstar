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

Inductive Tp {Vs : Set} : Set :=
  | Tp_var : Vs -> Tp
  | Tp_exp : Tp -> Tp -> Tp
  (* TODO allow constants like [I] and [bool] *)
.
Hint Constructors Tp.
Arguments Tp : default implicits.

Fixpoint eval_type {Ts Vs : Set} (a : Tp Ts) : Term Vs :=
  match a with
  | Tp_var v => (* TODO *) term_bot
  | Tp_exp a b => (* TODO *) term_bot
  end.

(* annotated normal forms *)
Inductive TNormal {Vs Ts : Set} : Set :=
  | TNormal_bot : TNormal
  | TNormal_join : TNormal -> TNormal -> TNormal
  | TNormal_rand : TNormal -> TNormal -> TNormal
  | TNormal_inert : TInert -> TNormal
  | TNormal_lambda : @TNormal (option Vs) Ts -> TNormal
  | TNormal_ann : Tp Ts -> TNormal -> TNormal
with TInert {Vs Ts : Set} : Set :=
  | TInert_var : Vs -> TInert
  | TInert_app : TInert -> TNormal -> TInert
  | TInert_ann : Tp Ts -> TInert -> TInert.
Hint Constructors TNormal TInert.
Arguments TNormal : default implicits.
Arguments TInert : default implicits.

Fixpoint eval_tnormal {Vs Ts : Set} (x : TNormal Vs Ts) : Term Vs :=
  match x with
  | TNormal_bot => term_bot
  | TNormal_join x1 x2 => term_join (eval_tnormal x1) (eval_tnormal x2)
  | TNormal_rand x1 x2 => term_rand (eval_tnormal x1) (eval_tnormal x2)
  | TNormal_inert i => eval_tinert i
  | TNormal_lambda x1 => term_lambda (eval_tnormal x1)
  | TNormal_ann a x1 => term_app (eval_type a) (eval_tnormal x1)
  end
with eval_tinert {Vs Ts : Set} (x : TInert Vs Ts) : Term Vs :=
  match x with
  | TInert_app x1 x2 => term_app (eval_tinert x1) (eval_tnormal x2)
  | TInert_var v => term_var v
  | TInert_ann a1 x1 => term_app (eval_type a1) (eval_tinert x1)
  end.

Fixpoint tnormal_map {Vs Vs' Ts : Set} (f : Vs -> Vs') (x : TNormal Vs Ts) :
  TNormal Vs' Ts :=
  match x with
  | TNormal_bot => TNormal_bot
  | TNormal_join x1 x2 => TNormal_join (tnormal_map f x1) (tnormal_map f x2)
  | TNormal_rand x1 x2 => TNormal_rand (tnormal_map f x1) (tnormal_map f x2)
  | TNormal_inert i => TNormal_inert (tinert_map f i)
  | TNormal_lambda x1 => TNormal_lambda (tnormal_map (option_map f) x1)
  | TNormal_ann a x1 => TNormal_ann a (tnormal_map f x1)
  end
with tinert_map {Vs Vs' Ts : Set}  (f : Vs -> Vs') (x : TInert Vs Ts) :
  TInert Vs' Ts :=
  match x with
  | TInert_app x1 x2 => TInert_app (tinert_map f x1) (tnormal_map f x2)
  | TInert_var v => TInert_var (f v)
  | TInert_ann a1 x1 => TInert_ann a1 (tinert_map f x1)
  end.

Definition tnormal_some_sub
  {Vs Vs' Ts : Set} (f : Vs -> TInert Vs' Ts) (v : option Vs) :
  TInert (option Vs') Ts :=
  match v with
  | None => TInert_var None
  | Some v' => tinert_map (@Some Vs') (f v')
  end.

Fixpoint
  tnormal_sub {Vs Vs' Ts : Set} (f : Vs -> TInert Vs' Ts) (x : TNormal Vs Ts) :
  TNormal Vs' Ts :=
  match x with
  | TNormal_bot => TNormal_bot
  | TNormal_join x1 x2 => TNormal_join (tnormal_sub f x1) (tnormal_sub f x2)
  | TNormal_rand x1 x2 => TNormal_rand (tnormal_sub f x1) (tnormal_sub f x2)
  | TNormal_inert i => TNormal_inert (tinert_sub f i)
  | TNormal_lambda x1 => TNormal_lambda (tnormal_sub (tnormal_some_sub f) x1)
  | TNormal_ann a x1 => TNormal_ann a (tnormal_sub f x1)
  end
with
  tinert_sub {Vs Vs' Ts : Set}  (f : Vs -> TInert Vs' Ts) (x : TInert Vs Ts) :
  TInert Vs' Ts :=
  match x with
  | TInert_app x1 x2 => TInert_app (tinert_sub f x1) (tnormal_sub f x2)
  | TInert_var v => f v
  | TInert_ann a1 x1 => TInert_ann a1 (tinert_sub f x1)
  end.

Definition ann_lambda {Vs Ts : Set} (a : Tp Ts) :
  TNormal (option Vs) Ts -> TNormal (option Vs) Ts :=
  tnormal_sub (
    fun v =>
    match v with
    | None => TInert_ann a (TInert_var None)
    | Some v => TInert_var (Some v)
    end).

Definition ann_lambda' {Vs Ts : Set} (a : Tp Ts) :
  TInert (option Vs) Ts -> TInert (option Vs) Ts :=
  tinert_sub (
    fun v =>
    match v with
    | None => TInert_ann a (TInert_var None)
    | Some v => TInert_var (Some v)
    end).

Inductive checks {Vs Ts : Set} : relation (TNormal Ts Vs) :=
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
  (* TODO
  (* How to deal with covariance vs contravariance? *)
  | checks_eta_expand :
  | checks_conjugate :
  | checks_identity :
  | checks_clash_var_var :
  | checks_clash_var_exp :
  | checks_clash_exp_var :
  *)
with checks' {Vs Ts : Set} : relation (TInert Ts Vs) :=
  (* TODO *)
.

Instance checks_sound (Vs Ts : Set) :
  Proper (checks --> term_le) (@eval_tnormal Vs Ts).
Proof.
  intros y x xy; induction xy; simpl; try (term_to_code; auto; reflexivity).
  - transitivity (eval_tnormal y); auto.
  - admit. (* TODO define [eval_type] *)
  - admit.
    (* TODO show [eval_type a (x (+) y) [= eval_type a x (+) eval_type a y]. *)
Qed.

Fixpoint check_step {Vs Ts : Set} (x : TNormal Ts Vs) :
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
with check_step' {Vs Ts : Set} (x : TInert Vs Ts) :
  option (TInert Vs Ts) :=
  match x with
  (* TODO
  | TInert_app x1 x2 => term_app (eval_tinert x1) (eval_tnormal x2)
  | TInert_var v => term_var v
  | TInert_ann a1 x1 => term_app (eval_type a1) (eval_tinert x1)
  *)
  | _ => None
  end.

Fixpoint check_step_checks (Vs Ts : Set) (x : TNormal Vs Ts) :
  match check_step x with
  | None => True
  | Some y => checks x y
  end
with check_step_checks' (Vs Ts : Set) (x : TInert Vs Ts) :
  match check_step' x with
  | None => True
  | Some y => checks' x y
  end.
Proof.
  - admit.
  - admit.
Admitted.

Fixpoint try_check {Vs Ts : Set} (n : nat) (x : TNormal Vs Ts) :
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
Instance checks_complete (Vs Ts : Set) (x y : TNormal Vs Ts) : ???
*)

(* FIXME
Definition fixes {Vs Ts : Set} (a : Tp Ts) (x : TNormal Ts Vs) : Prop :=
  checks (TNormal_ann a x) x.
*)
