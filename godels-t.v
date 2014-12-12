
Inductive tp : Set :=
  | tp_nat: tp
  | tp_exp: tp -> tp -> tp.
Hint Constructors tp.

Notation "t -o t0" := (tp_exp t t0) (at level 51, right associativity).

Inductive term : tp -> Set :=
  | ap: forall {a b : tp}, term (a -o b) -> term a -> term b
  | sub: forall {a b c : tp}, term ((a -o b -o c) -o (a -o b) -o a -o c)
  | const: forall {a b : tp}, term (a -o b -o a)
  | zero: term tp_nat
  | succ: term (tp_exp tp_nat tp_nat)
  | rec: forall {a : tp}, term (tp_nat -o (tp_nat -o a -o a) -o a -o a).
Hint Constructors term.

Notation "x * y" := (ap x y) (at level 40, left associativity).

Fixpoint eval_tp (a : tp) : Type :=
  match a with
    | tp_nat => nat
    | a -o a0 => (eval_tp a) -> (eval_tp a0)
  end.

(* this fails to type check *)
Inductive step {a : tp} : term a -> term a -> Set :=
  | step_k: forall {b : tp} x y, step ((@const a b)*x*y) x
  | step_subs: forall {b c : tp} x y z, step ((@sub b c a)*x*y*z) (x*z*(y*z))
  | step_zero: forall f x, step (rec*zero*f*x) x
  | step_succ: forall f x n, step (rec*(succ*n)*f*x) (f*n*(rec*n*f*x)).
Hint Constructors step.

(* Tait's hereditarily strongly normalizing predicate *)
Inductive safe : forall {a : tp}, term a -> Prop :=
  | safe_nat: forall x : term tp_nat,
      (forall y, step x y -> safe y) -> safe x
  | safe_exp: forall {a b : tp} (f : term (a -o b)),
      (forall x, safe (f*x)) -> safe f.
Hint Constructors safe.

Theorem safety: forall a (x : term a), safe x.
Proof.
  induction x.
  inversion IHx1.
  (* TODO *)

  induction H.
  apply H0 with (f := x1).
  apply (safe_exp x1).
  apply safe_exp with (f := safe).
  
  induction a.
  auto.
  (* TODO *)
Qed.
