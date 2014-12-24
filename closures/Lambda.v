(** * Translation [Ob <-> Lambda].

    This demonstrates a simple way to write combinators using lambda notation,
    but does not allow any direct reasoning about lambda Lambdas.
    The main trick is to embed inline-assembly-style Ob blocks
    in lambda Lambdas via a [OB] constructor.
    *)

Require Import ObAxioms.
Require Import EqNat.

Inductive Lambda : Set :=
| OB : Ob -> Lambda
| VAR : nat -> Lambda
| ABS : nat -> Lambda -> Lambda
| APP : Lambda -> Lambda -> Lambda.

Definition abs (x : Lambda) (y : Lambda) : Lambda :=
  match x with
  | VAR n => ABS n y
  | z => OB TOP
  end.

Section Encode.
  Notation "[ x ]" := (OB x).
  Notation "x [*] y" := (APP x y) (at level 40, left associativity).

  Fixpoint abstract (n : nat) (x : Lambda) : Lambda :=
    match x with
    | VAR m => if beq_nat m n then [I] else [K] [*] (VAR m)
    | ABS m y => if beq_nat m n then [K] [*] (ABS m y) else ABS m (abstract n y)
    | APP y z => [S] [*] (abstract n y) [*] (abstract n z)
    | y => [K] [*] y
    end.

  Fixpoint compile (x : Lambda) : Lambda :=
    match x with
    | APP y z => APP (compile y) (compile z)
    | ABS n y => abstract n (compile y)
    | y => y
    end.

  Fixpoint close (x : Lambda) : Ob :=
    match x with
    | OB y => y
    | APP y z => AP (close y) (close z)
    | _ => TOP
    end.

  Definition encode x := close (compile x).
End Encode.

Notation "x * y" := (APP x y) (at level 40, left associativity) : Lambda_scope.
Delimit Scope Lambda_Scope with Lambda.
Bind Scope Lambda_Scope with Lambda.
Local Open Scope Lambda_scope.

Notation "\ x , y" := (abs x y) (at level 60, right associativity) : Lambda_scope.
Notation "x 'o' y" := (APP x y) (at level 30, right associativity) : Lambda_scope.
Notation "x || y" := ((OB J) * x * y) (at level 50, left associativity) : Lambda_scope.
Notation "x (+) y" := ((OB R) * x * y) (at level 45, no associativity) : Lambda_scope.

Section combinators.
  Notation "'x'" := (VAR 0) : Lambda_scope.
  Notation "'y'" := (VAR 1) : Lambda_scope.
  Notation "'z'" := (VAR 2) : Lambda_scope.

  Let TOP' := OB TOP.
  Let S' := \x,\y,\z, x*z*(y*z).
  Let K' := \x,\y, x.
  Let I' := \x, x.
  Let B' := \x,\y,\z, x*(y*z).
  Let C' := \x,\y,\z, x*z*y.
  Let Y' := \x, (\y, x*(y*y)) * (\y, x*(y*y)).
  Let V' := Y' * \x,\y, I' || x o y.
  Let div' := Y' * \x, x * TOP'.

  Definition B := encode B'.
  Definition C := encode C'.
  Definition Y := encode Y'.
  Definition V := encode V'.
  Definition div := encode div'.
End combinators.
