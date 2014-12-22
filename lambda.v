Inductive code : Set :=
| TOP : code
| S : code
| K : code
| I : code
| AP : code -> code -> code.

Notation "x * y" := (AP x y) (at level 40, left associativity).

Inductive term : Set :=
| CODE : code -> term
| VAR : nat -> term
| ABS : nat -> term -> term
| APP : term -> term -> term.

Notation "[ x ]" := (CODE x).
Notation "x [*] y" := (APP x y) (at level 40, left associativity).

Require Import EqNat.

Fixpoint abstract (n : nat) (e : term) : term :=
  match e with
  | [x] => [K * x]
  | VAR n' => if beq_nat n n' then [I] else [K] [*] (VAR n')
  | e0 [*] e1 => [S] [*] (abstract n e0) [*] (abstract n e1)
  | ABS n' e0 => ABS n' (abstract n e0)
  end.

(* FIXME
Fixpoint encode (e : term) : code :=
  match e with
  | [x] => x
  | VAR n => TOP
  | e [*] e0 => (encode e) * (encode e0)
  | ABS n e => encode (abstract n e)
  end.
*)
