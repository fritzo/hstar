Require Import ObAxioms.

Ltac reduce n := admit. (* TODO *)

(*
Fixpoint reduce_step (e : Ob) : option Ob :=
  match goal with
  | I * x => x
  | S * x * y * z => x * y * (x * z)
  | _ => None
  end.

Ltac reduce' n :=
  match n with
  | 0%nat => idtac
  | Succ n0 => reduce_step
  end.
*)
