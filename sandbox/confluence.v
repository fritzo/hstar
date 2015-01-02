(** Confluence of beta-reduction in combinatory algebra.

    TODO declare [red] to be reflexive and transitive,
    as described in https://coq.inria.fr/refman/Reference-Manual029.html
*)

Inductive term :=
  | S : term
  | K : term
  | AP : term -> term -> term.
Hint Constructors term.

Notation "x * y" := (AP x y) (at level 40, left associativity).

Inductive step : term -> term -> Prop :=
  | step_s: forall x y z, step (S * x * y * z) (x * z * (y * z))
  | step_k: forall x y, step (K * x * y) x
  | step_ap_1: forall x x0 y, step x x0 -> step (x * y) (x0 * y)
  | step_ap_2: forall x y y0, step y y0 -> step (x * y) (x * y0).
Hint Constructors step.

Inductive red : term -> term -> Prop :=
  | red_refl: forall x, red x x
  | red_trans: forall x y z, red x y -> step y z -> red x z.
Hint Constructors red.

Lemma confluence_step_step:
  forall x y y0,
  step x y -> step x y0 -> exists z, red y z /\ red y0 z.
Proof.
  intros.
  inversion H; inversion H0.
  exists (x0 * z * (y1 * z)).
  split; reflexivity.
  auto.
  apply step_s .


Theorem confluence:
  forall x y y0,
  red x y -> red x y0 -> exists z, red y z /\ red y0 z.
Proof.
  intros.
  (* TODO *)
Qed.

