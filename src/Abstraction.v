Require Import EqNat.
Require Import Codes.

(** * Sloppy lambda notation specialized to [Code nat] *)

Definition nat_match (m n : nat) : option nat :=
  if beq_nat m n then None else Some m.

Definition code_lambda (v : Code nat) (x : Code nat) : Code nat :=
  match v with
  | code_var n => code_abs (nat_match n) x
  | _ => code_top (* TODO implement pattern matching here*)
  end.

Notation "\ x , y" := (code_lambda x y)%code : code_scope.
