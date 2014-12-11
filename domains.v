(* an attempt at domain theory *)

CoInductive Partial (A : Set) : Set :=
  | Find : A -> Partial A
  | Wait : Partial A -> Partial A.

Definition find {A : Set} := Find A.
Definition wait {A : Set} := Wait A.
CoFixpoint diverge {A : Set} : Partial A := wait diverge.

CoInductive partial_leq {A : Set} : Partial A -> Partial A -> Prop :=
  | partial_leq_find : forall a, partial_leq (find a) (find a)
  | partial_leq_wait : forall p q, partial_leq p q -> partial_leq (wait p) q
  | partial_leq_wait_wait :
    forall p q, partial_leq p q -> partial_leq (wait p) (wait q).

Definition partial_continuous (A : Set) (B : Set) :=
  forall f : Partial A -> Partial B,
  forall x y : Partial A,
  partial_leq x y -> partial_leq (f x) (f y).

Lemma partial_leq_refl : forall A (x : Partial A), partial_leq x x.
  cofix.
  intros.
  destruct x.
  apply partial_leq_find.
  apply partial_leq_wait_wait.
  apply partial_leq_refl.
Qed.

Lemma partial_leq_trans {A : Set} : forall x y z : Partial A,
  partial_leq x y -> partial_leq y z -> partial_leq x z.
  intros x y z.
  cofix.
  destruct x.
  (* TODO *)
Admitted.

Lemma unfold_diverge : forall A, @diverge A = wait diverge.
  intros.
  unfold diverge at 1.
  unfold diverge at 1.
