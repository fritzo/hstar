(** This demonstrates a simple way to write combinators using lambda notation,
    but does not allow any direct reasoning about lambda terms *)

Require Import EqNat.

Inductive code : Set :=
| TOP : code
| S : code
| K : code
| I : code
| R : code
| J : code
| AP : code -> code -> code.

Inductive term : Set :=
| CODE : code -> term
| VAR : nat -> term
| ABS : nat -> term -> term
| APP : term -> term -> term.

Definition abs (x : term) (y : term) : term :=
  match x with
  | VAR n => ABS n y
  | z => CODE TOP
  end.

Section Encode.
  Notation "[ x ]" := (CODE x).
  Notation "x [*] y" := (APP x y) (at level 40, left associativity).

  Fixpoint abstract (n : nat) (x : term) : term :=
    match x with
    | VAR m => if beq_nat m n then [I] else [K] [*] (VAR m)
    | ABS m y => if beq_nat m n then [K] [*] (ABS m y) else ABS m (abstract n y)
    | APP y z => [S] [*] (abstract n y) [*] (abstract n z)
    | y => [K] [*] y
    end.

  Fixpoint compile (x : term) : term :=
    match x with
    | APP y z => APP (compile y) (compile z)
    | ABS n y => abstract n (compile y)
    | y => y
    end.

  Fixpoint close (x : term) : code :=
    match x with
    | CODE y => y
    | APP y z => AP (close y) (close z)
    | _ => TOP
    end.

  Definition encode x := close (compile x).
End Encode.

Section combinators.
  Notation "\ x , y" := (abs x y) (at level 60, right associativity).
  Notation "x 'o' y" := (APP x y) (at level 35, right associativity).
  Notation "x * y" := (APP x y) (at level 40, left associativity).
  Notation "x || y" := ((CODE J) * x * y) (at level 50, left associativity).
  Notation "x (+) y" := ((CODE R) * x * y) (at level 45, no associativity).

  Let x := VAR 0.
  Let y := VAR 1.
  Let z := VAR 2.

  Definition TOP' := CODE TOP.
  Definition S' := \x,\y,\z, x*z*(y*z).
  Definition K' := \x,\y, x.
  Definition I' := \x, x.
  Definition B' := \x,\y,\z, x*(y*z).
  Definition C' := \x,\y,\z, x*z*y.
  Definition Y' := \x, (\y, x*(y*y)) * (\y, x*(y*y)).
  Definition V' := Y' * \x,\y, I' || x o y.
  Definition div' := Y' * \x, x * TOP'.

  Definition B := encode B'.
  Definition C := encode C'.
  Definition Y := encode Y'.
  Definition V := encode V'.
  Definition div := encode div'.
End combinators.
