Require Import BohmTrees.

(* for reference
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

Inductive normal {Var : Set} : Term Var -> Prop :=
  | normal_bot : normal BOT
  | normal_join x y : normal x -> normal y -> normal (x || y)
  | normal_rand x y : normal x -> normal y -> normal (x (+) y)
  | normal_app x y : inert x -> normal y -> normal (x * y)
  | normal_lambda x : @normal (option Var) x -> normal (LAMBDA x)
  | normal_var v : normal (VAR v)
with inert {Var : Set} : Term Var -> Set :=
  | inert_var v : inert (VAR v)
  | inert_app x y : inert x -> normal y -> inert (x * y).
Hint Constructors normal inert.
*)

Inductive Normal {Var : Set} : Set :=
  | Normal_bot : Normal
  | Normal_join : Normal -> Normal -> Normal
  | Normal_rand : Normal -> Normal -> Normal
  | Normal_app : Inert -> Normal -> Normal
  | Normal_lambda : @Normal (option Var) -> Normal
  | Normal_var : Var -> Normal
with Inert {Var : Set} : Set :=
  | Inert_var : Var -> Inert
  | Inert_app : Inert -> Normal -> Inert.
Hint Constructors Normal Inert.
Arguments Normal : default implicits.
Arguments Inert : default implicits.

Inductive Tp {Var : Set} : Set :=
  | Tp_any : Tp
  | Tp_exp : Tp -> Tp -> Tp
  | Tp_var : Var -> Tp.
Hint Constructors Tp.
Arguments Tp : default implicits.

Inductive TNormal {TVar Var : Set} : Set :=
  | TNormal_bot : Tp TVar -> TNormal
  | TNormal_join : Tp TVar -> TNormal -> TNormal -> TNormal
  | TNormal_rand : Tp TVar -> TNormal -> TNormal -> TNormal
  | TNormal_app : Tp TVar -> TInert -> TNormal -> TNormal
  | TNormal_lambda : Tp TVar -> @TNormal TVar (option Var) -> TNormal
  | TNormal_var : Tp TVar -> Var -> TNormal
with TInert {TVar Var : Set} : Set :=
  | TInert_var : Tp TVar -> Var -> TInert
  | TInert_app : Tp TVar -> TInert -> TNormal -> TInert.
Hint Constructors TNormal TInert.
Arguments TNormal : default implicits.
Arguments TInert : default implicits.

Fixpoint annotate_any {TVar Var : Set} (n : Normal Var) : TNormal TVar Var :=
  match n with
  | Normal_bot => TNormal_bot Tp_any
  | Normal_join x y => TNormal_join Tp_any (annotate_any x) (annotate_any y)
  | Normal_rand x y => TNormal_rand Tp_any (annotate_any x) (annotate_any y)
  | Normal_app x y => TNormal_app Tp_any (annotate_any' x) (annotate_any y)
  | Normal_lambda x => TNormal_lambda Tp_any (annotate_any x)
  | Normal_var v => TNormal_var Tp_any v
  end
with annotate_any' {TVar Var : Set} (i : Inert Var) : TInert TVar Var :=
  match i with
  | Inert_var v => TInert_var Tp_any v
  | Inert_app x y => TInert_app Tp_any (annotate_any' x) (annotate_any y)
  end.
