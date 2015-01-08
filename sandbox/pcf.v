Require Import EqNat.

Inductive tp : Set :=
  | tp_nat : tp
  | tp_exp : tp -> tp -> tp.

Notation "a --> b" := (tp_exp a b) (at level 51, right associativity).

Fixpoint beq_tp (a b : tp) : bool :=
  match a, b with
  | tp_nat, tp_nat => true
  | a0 --> a1, b0 --> b1 => andb (beq_tp a0 b0) (beq_tp a1 b1)
  | _, _ => false
  end.

Inductive term : tp -> Set :=
  | term_var a : nat -> term a
  | term_app a b : term (a --> b) -> term a -> term b
  | term_abs a b : nat -> term b -> term (a --> b)
  | term_let a b : nat -> term a -> term b -> term b
  | term_zero : term tp_nat
  | term_succ : term (tp_nat --> tp_nat)
  | term_pred : term (tp_nat --> tp_nat)
  | term_ifz a : term tp_nat -> term a -> term a -> term a
  | term_fix a : term (a --> a) -> term a
  | term_join a : term a -> term a -> term a
  | term_rand a : term a -> term a -> term a.

(* This fails to type check
Fixpoint subs {a : tp} (x : term a) :
  forall nb : nat * tp, term (snd nb) -> term a :=
  let s := subs in
  match x with
  | term_var a n => fun na' =>
      let (n', a') := na' in
      if andb (beq_nat n n') (beq_tp a a')
      then fun y => y
      else fun y => x
  | term_app a b x0 x1 => fun na y =>
      term_app a b (s x0 na y) (s x1 na y)
  | term_abs a b n x0 => fun na' y =>
      let (n', a') := na' in
      if andb (beq_nat n n') (beq_tp a a')
      then x
      else term_abs a b n (s x0 na' y)
  | term_let a b n z0 x0 => fun na' y =>
      let (n', a') := na' in
      if andb (beq_nat n n') (beq_tp a a')
      then term_let a b n (s z0 na' y) x0
      else term_let a b n (s z0 na' y) (s x0 na' y)
  | term_zero => fun na y => term_zero
  | term_succ => fun na y => term_succ
  | term_pred => fun na y => term_pred
  | term_ifz a x0 x1 x2 => fun na y =>
      term_ifz (s x0 na y) (s x1 na y) (s x2 na y)
  | term_fix a x0 => fun na y => fun na y =>
      term_fix a (s x0 na y)
  | term_join a x0 x1 => fun na y =>
      term_app (s x0 na y) (s x1 na y)
  | term_rand a x0 x1 => fun na y =>
      term_app (s x0 na y) (s x1 na y)
  end.
*)

(* This fails to type check
Fixpoint subs {a b : tp} (v : nat) (x : term a) (y : term b) : term b :=
  let s := subs v x in
  match y with
  | term_var a v' => if beq_nat v v' then x else y
  | term_app a b y0 y1 => term_app a b (s y0) (s y1)
  | term_abs a b v' y0 => if beq_nat v v' then y else term_abs a b v (s y0)
  | term_let a b v' x0 y0 =>
      if beq_nat v v'
      then term_let a b v (s x0) y0
      else term_let a b v (s x0) (s y0)
  | term_zero => term_zero
  | term_succ => term_succ
  | term_pred => term_pred
  | term_ifz a y0 y1 y2 => term_ifz (s y0) (s y1) (s y2)
  | term_fix a y0 => term_fix a (s y0)
  | term_join a y0 y1 => term_app (s y0) (s y1)
  | term_rand a y0 y1 => term_app (s y0) (s y1)
  end.
*)

(*
Inductive step : forall a, term a -> term a -> Set :=
  | step_
*)
