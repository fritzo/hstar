(* an attempt at domain theory *)

CoInductive Partial (A : Set) : Set :=
  | Find : A -> Partial A
  | Wait : Partial A -> Partial A.

Definition find {A : Set} := Find A.
Definition wait {A : Set} := Wait A.
CoFixpoint diverge {A : Set} : Partial A := wait diverge.

CoInductive leq_partial {A : Set} : Partial A -> Partial A -> Prop :=
  | leq_partial_find : forall a, leq_partial (find a) (find a)
  | leq_partial_wait : forall p q, leq_partial p q -> leq_partial (wait p) q
  | leq_partial_wait_wait :
    forall p q, leq_partial p q -> leq_partial (wait p) (wait q).

Definition partial_cont (A : Set) (B : Set) :=
  forall f : Partial A -> Partial B,
  forall x y : Partial A,
  leq_partial x y -> leq_partial (f x) (f y).

Lemma partial_leq_refl : forall A (x : Partial A), leq_partial x x.
  cofix.
  intros.
  destruct x.
  apply leq_partial_find.
  apply leq_partial_wait_wait.
  apply partial_leq_refl.
Qed.

Lemma partial_leq_trans {A : Set} : forall x y z : Partial A,
  leq_partial x y -> leq_partial y z -> leq_partial x z.
  intros x y z.
  cofix.
  destruct x.
  TODO

Lemma unfold_diverge : forall A, diverge A = Wait A (diverge A).
intros.
 unfold diverge at 1.
unfold diverge at 1.