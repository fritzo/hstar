Require Import Coq.Program.Basics.
Require Import Coq.Program.Equality.
Require Import Coq.Setoids.Setoid.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Logic.Decidable.
Require Import Coq.Bool.Bool.

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

Inductive Normal {Vs : Set} : Set :=
  | Normal_bot : Normal
  | Normal_join : Normal -> Normal -> Normal
  | Normal_lambda : @Normal (option Vs) -> Normal
  | Normal_inert : Inert -> Normal
with Inert {Vs : Set} : Set :=
  | Inert_var : Vs -> Inert
  | Inert_app : Inert -> Normal -> Inert.
Hint Constructors Normal Inert.
Arguments Normal : default implicits.
Arguments Inert : default implicits.

Inductive Tp {Vs : Set} : Set :=
  | Tp_var : Vs -> Tp
  | Tp_exp : Tp -> Tp -> Tp.
Hint Constructors Tp.
Arguments Tp : default implicits.

(* annotated normal forms *)
Inductive TNormal {Vs Ts : Set} : Set :=
  | TNormal_bot : TNormal
  | TNormal_join : TNormal -> TNormal -> TNormal
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

Fixpoint ann_lambda {Vs Ts : Set} (a : Tp Ts) (x : TNormal (option Vs) Ts) :
  TNormal (option Vs) Ts :=
  match x with
  | TNormal_bot => TNormal_bot
  | TNormal_join x1 x2 => TNormal_join (ann_lambda a x1) (ann_lambda a x2)
  | TNormal_inert i => TNormal_inert (ann_lambda' a i)
  | TNormal_lambda v => (* TODO use option_map *) TNormal_bot
  | TNormal_ann a1 x1 => TNormal_ann a1 (ann_lambda a x1)
  end
with ann_lambda' {Vs Ts : Set} (a : Tp Ts) (x : TInert (option Vs) Ts) :
 TInert (option Vs) Ts :=
  match x with
  | TInert_app x1 x2 => TInert_app (ann_lambda' a x1) (ann_lambda a x2)
  | TInert_var None => TInert_ann a (TInert_var None)
  | TInert_var (Some v) => TInert_var (Some v)
  | TInert_ann a1 x1 => TInert_ann a1 (ann_lambda' a x1)
  end.

Inductive check {Vs Ts : Set} : relation (TNormal Ts Vs) :=
  | check_refl x : check x x
  | check_trans x y z : check x y -> check y z -> check x z
  | check_bot x : check x TNormal_bot
  | check_join_left x y : check (TNormal_join x y) x
  | check_join_right x y : check (TNormal_join x y) y
  (* ...app etc... *)
  | check_expand_lambda a b x :
      check (TNormal_ann (Tp_exp a b) (TNormal_lambda x))
            (TNormal_lambda (TNormal_ann b (ann_lambda a x)))

  | check_expand_join a x y :
      check (TNormal_ann a (TNormal_join x y))
            (TNormal_join (TNormal_ann a x) (TNormal_ann a y))
  (* TODO
  (* How to deal with covariance vs contravariance? *)
  | check_eta_expand :
  | check_conjugate :
  | check_identity :
  | check_clash_var_var :
  | check_clash_var_exp :
  | check_clash_exp_var :
  *)
.

(* FIXME
Definition fixes {Vs Ts : Set} (a : Tp Ts) (x : TNormal Ts Vs) : Prop :=
  check (TNormal_ann a x) x.
*)
