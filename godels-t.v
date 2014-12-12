
Inductive tp : Set :=
  | tp_nat: tp
  | tp_exp: tp -> tp -> tp.

Notation "t -o t0" := (tp_exp t t0) (at level 51, right associativity).

Inductive term : tp -> Set :=
  | ap: forall {a b : tp}, term (a -o b) -> term a -> term b
  | sub: forall {a b c : tp}, term ((a -o b -o c) -o (a -o b) -o a -o c)
  | const: forall {a b : tp}, term (a -o b -o a)
  | zero: term tp_nat
  | succ: term (tp_exp tp_nat tp_nat)
  | rec: forall {a : tp}, term (tp_nat -o (tp_nat -o a -o a) -o a -o a).

Notation "x * y" := (ap x y) (at level 40, left associativity).

Fixpoint eval_tp (a : tp) : Type :=
  match a with
    | tp_nat => nat
    | a -o a0 => (eval_tp a) -> (eval_tp a0)
  end.

(* this fails to type check *)
Inductive step {a : tp} : term a -> term a -> Set :=
  | red_k: forall {b : tp} (x : a -o b)) y, step (const*x*y) x
  | red_subs: forall x y z, step (S*x*y*z) (x*z*(y*z))
  | red_zero: forall f x, step (rec*x*f*zero) x
  | red_succ: forall f x y, step (rec*x*f*(succ*y)) (f*y*(rec*x*f*y)).
