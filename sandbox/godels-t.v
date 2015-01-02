
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

Fixpoint eval_tp (a : tp) : Set :=
  match a with
    | tp_nat => nat
    | a -o a0 => (eval_tp a) -> (eval_tp a0)
  end.

Inductive step : forall {a}, term a -> term a -> Set :=
  | step_ap_1: forall {a b} (f f0 : term (b -o a)) (x : term b),
    step f f0 -> step (f*x) (f0*x)
  | step_ap_2: forall {a b} (f : term (b -o a)) (x x0 : term b),
    step x x0 -> step (f*x) (f*x0)
  | step_const: forall {a b} x y, step ((@const a b)*x*y) x
  | step_subs: forall {a b c} x y z, step ((@sub b c a)*x*y*z) (x*z*(y*z))
  | step_zero: forall {a} f x, step ((@rec a)*zero*f*x) x
  | step_succ: forall {a} f x n, step ((@rec a)*(succ*n)*f*x) (f*n*(rec*n*f*x)).
Hint Constructors step.

Inductive terminates {a} (x : term a) : Prop :=
  terminates_intro: (forall y, step x y -> terminates y) -> terminates x.
Hint Constructors terminates.

Ltac value :=
  match goal with
  | [  |- terminates ?X ] => apply terminates_intro; intros y H; inversion H
  end.

Lemma const_val {a b}: terminates (@const a b).
Proof.  value.  Qed.

Lemma const_x_val {a b}:
  forall x, terminates x -> terminates ((@const a b) * x).
Proof.
  intros.
  apply terminates_intro.
  intros.
  inversion H0.
  (* TODO *)
Admitted.

(* Tait's hereditary termination predicate *)
Inductive hterminates : forall {a}, term a -> Prop :=
  | hterminates_nat: forall (x : term tp_nat),
    terminates x -> hterminates x
  | hterminates_exp: forall {a b} (f : term (a -o b)),
 (* FIXME *)
 (* terminates f -> (forall x, hterminates x -> hterminates (f*x)) -> *)
    terminates f -> (forall x, terminates x -> hterminates (f*x)) ->
    hterminates f.
Hint Constructors hterminates.

Lemma hterminates_ap: forall {a b} (x : term (a -o b)) (y : term a),
  hterminates x -> hterminates y -> hterminates (x * y).
Proof.
  intros.
  inversion H.
  (* TODO get rid of existT in hypothesis *)
Admitted.
Hint Resolve hterminates_ap.

Theorem hereditary_termination: forall a (x : term a), hterminates x.
Proof.
  induction x.
  inversion IHx1.
  apply hterminates_ap; assumption.
  assert (terminates (@sub a b c)).
  apply terminates_intro.
  intros.
  inversion H.
  destruct 1.
  (* TODO *)
Qed.
