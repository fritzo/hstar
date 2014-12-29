(** * Bohm Trees *)

Require Import ObAxioms.
Require Import Lambda.

Inductive hnf : Ob -> Prop :=
  | hnf_TOP: hnf TOP
  | hnf_K: hnf K
  | hnf_Kx x: hnf (K * x)
  | hnf_S: hnf S
  | hnf_Sx x: hnf x -> hnf (S * x)
  | hnf_Sxy x y: hnf x -> hnf (S * x * y)
  | hnf_Rxy x y: hnf x -> hnf y -> hnf (x(+)y)
  | hnf_Jxy x y: hnf x -> hnf y -> hnf (x||y)
  | hnf_Join (s : Set) (e : s -> Ob): (forall i, hnf (e i)) -> hnf (Join e).

Theorem hnf_conv: forall x : Ob, conv x -> {y : Ob & y [= x & hnf y}.
Proof.
  intros x Hconv.
  (* FIXME why does this fail?
  elim Hconv.
  *)
  (* TODO *)
Admitted.
