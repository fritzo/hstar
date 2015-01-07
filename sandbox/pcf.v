Require Import EqNat.

Inductive tp : Set :=
  | tp_nat : tp
  | tp_exp : tp -> tp -> tp.

Notation "a --> b" := (tp_exp a b) (at level 51, right associativity).

Inductive term : tp -> Set :=
  | term_var (a : tp) : nat -> term a
  | term_app (a b : tp) : term b -> term (a --> b)
  | term_abs (a b : tp) : nat -> term b -> term (a --> b)
  | term_let (a b : tp) : nat -> term a -> term b -> term b
  | term_zero : term tp_nat
  | term_succ : term (tp_nat --> tp_nat)
  | term_pred : term (tp_nat --> tp_nat)
  | term_ifz a : term tp_nat -> term a -> term a -> term a
  | term_fix a : term (a --> a) -> term a
  | term_join a : term a -> term a -> term a
.

(*
Fixpoint subs {a b : tp} (v : nat) (x : term a) (y : term b) : term b :=
  match y with
  | term_var a v => 

Inductive step : forall a, term a -> term a -> Set :=
  | step_
*)
