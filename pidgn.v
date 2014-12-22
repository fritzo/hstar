Require Import EqNat.

Inductive Term : Set :=
| TOP : Term
| S : Term
| K : Term
| I : Term
| AP : Term -> Term -> Term
| ABS : nat -> Term -> Term
| VAR : nat -> Term.

Definition abs (x : Term) (y : Term) : Term :=
  match x with
  | VAR n => ABS n y
  | z => TOP
  end.

Fixpoint abstract (n : nat) (x : Term) : Term :=
  match x with
  | VAR m => if beq_nat m n then I else AP K (VAR m)
  | ABS m y => if beq_nat m n then AP K (ABS m y) else ABS m (abstract n y)
  | AP y z => AP (AP S (abstract n y)) (abstract n z)
  | y => AP K y
  end.

Fixpoint compile (x : Term) : Term :=
  match x with
  | AP y z => AP (compile y) (compile z)
  | ABS n y => abstract n (compile y)
  | y => y
  end.

Fixpoint close (x : Term) : Term :=
  match x with
  | AP y z => AP (close y) (close z)
  | VAR n => TOP
  | y => y
  end.

Definition encode x := close (compile x).

Notation "x * y" := (AP x y) (at level 40, left associativity).
Notation "[ x ] y" := (abs x y) (at level 50).

Section combinators.
  Let x := VAR 0.
  Let y := VAR 1.
  Let z := VAR 2.

  Definition S' := [x][y][z] x*z*(y*z).
  Definition K' := [x][y] x.
  Definition I' := [x] x.
  Definition B' := [x][y][z] x*(y*z).
  Definition C' := [x][y][z] x*z*y.
  Definition Y' := [x] ([y] x * (y * y)) * ([y] x * (y * y)).

  Definition B := encode B'.
  Definition C := encode C'.
  Definition Y := encode Y'.

  Fixpoint decode (e : Term) : Term :=
    match e with
    | TOP => TOP
    | S => S'
    | K => K'
    | I => I'
    | AP e0 e1 => AP (decode e0) (decode e1)
    | ABS n e0 => ABS n (decode e0)
    | VAR n => VAR n
    end.
End combinators.


