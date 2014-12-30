(** * Bohm Trees *)

Require Import ObAxioms.
Require Import Lambda.

Inductive hnf : Ob -> Type :=
  | hnf_TOP: hnf TOP
  | hnf_K: hnf K
  | hnf_Kx x: definable x -> hnf (K * x)
  | hnf_S: hnf S
  | hnf_Sx x: hnf x -> hnf (S * x)
  | hnf_Sxy x y: hnf x -> definable y -> hnf (S * x * y)
  | hnf_Rxy x y: hnf x -> hnf y -> hnf (x(+)y)
  | hnf_Jxy x y: hnf x -> hnf y -> hnf (x||y)
(*| hnf_Join (s : Set) (e : s -> Ob): (forall i, hnf (e i)) -> hnf (Join e)*)
.
Hint Constructors hnf.

Lemma hnf_definable: forall x, hnf x -> definable x.
Proof.
  intros x H; induction H; auto.
Qed.

Theorem hnf_conv:
  forall f x : Ob, conv (f * x) ->
  {y : Ob & y [= x & ((hnf y) * (conv (f * y)))%type}.
Proof.
  intros f x Hconv.
  inversion Hconv.
  (* TODO *)
Admitted.
