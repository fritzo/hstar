(** * Combinators [<->] lambda-terms.

    This demonstrates a simple way to write combinators using lambda notation,
    but does not allow any direct reasoning about lambda terms.
    The main trick is to embed inline-assembly-style code blocks
    in lambda terms via a [INLINE] constructor.
    *)

Require Import EqNat.

Inductive code : Set :=
  | I : code
  | K : code
  | B : code
  | C : code
  | W : code
  | S : code
  | J : code
  | BOT : code
  | TOP : code
  | AP : code -> code -> code.

Inductive Term {extend : Set} : Set :=
  | VAR: nat -> Term
  | APP: Term -> Term -> Term
  | ABS: nat -> Term -> Term
  | DEF: nat -> Term -> Term -> Term
  | ERROR: Term
  | HOLE: Term
  | JOIN: Term -> Term -> Term
  | INLINE: extend -> Term.

Definition term_ (e : Set) := Term (extend := e).
Definition term := term_ Empty_set.
Definition term' := term_ code.

(** The [term_] monad *)
Definition inline (a : Set) : a -> term_ a := fun x => INLINE x.
Fixpoint coerce {a b : Set} (f : a -> term_ b) (x : term_ a) : term_ b :=
  match x with
  | VAR n => VAR n
  | APP x0 x1 => APP (coerce f x0) (coerce f x1)
  | ABS n x0 => ABS n (coerce f x0)
  | DEF n x0 x1 => DEF n (coerce f x0) (coerce f x1)
  | ERROR => ERROR
  | HOLE => HOLE
  | JOIN x0 x1 => JOIN (coerce f x0) (coerce f x1)
  | INLINE x0 => f x0
  end.

Definition var (n : nat) : term := VAR n.
Definition app (x y : term) := APP x y.
Definition abs (x y : term) : term :=
  match x with
  | VAR n => ABS n y
  | z => HOLE
  end.
Definition join (x y : term) := JOIN x y.
Definition error : term := ERROR.
Definition hole : term := HOLE.


Section Encode.
  Notation "[ x ]" := (INLINE x).
  Notation "x [*] y" := (APP x y) (at level 40, left associativity).

  Fixpoint occurs (n : nat) (x : term') : bool :=
    match x with
    | VAR n0 => beq_nat n n0
    | APP x0 x1 => orb (occurs n x0) (occurs n x1)
    | ABS n0 x0 => andb (negb (beq_nat n n0)) (occurs n x0)
    | JOIN x0 x1 => orb (occurs n x0) (occurs n x1)
    | _ => false
    end.

  (* TODO implement prettier abstraction *)
  Fixpoint abstract (n : nat) (x : term') : term' :=
    match x with
    | VAR m => if beq_nat m n then [I] else [K] [*] (VAR m)
    | ABS m y =>
        if beq_nat m n
        then [K] [*] (ABS m y)
        else ABS m (abstract n y)
    | DEF m y z =>
        if beq_nat m n
        then [K] [*] (DEF m y z)
        else ERROR (* TODO *)
    | APP y z => [S] [*] (abstract n y) [*] (abstract n z)
    | JOIN y z => [J] [*] (abstract n y) [*] (abstract n z)
    | y => [K] [*] y
    end.

  Fixpoint compile (x : term') : term' :=
    match x with
    | APP y z => APP (compile y) (compile z)
    | ABS n y => abstract n (compile y)
    | y => y
    end.

  Fixpoint close (x : term') : code :=
    match x with
    | INLINE y => y
    | APP y z => AP (close y) (close z)
    | _ => TOP
    end.

  Definition noop (x : Empty_set) : term' := match x with end.
  Definition encode (x : term) : code := close(compile(coerce noop x)).
End Encode.

Section combinators.
  Notation "\ x , y" := (abs x y) (at level 60, right associativity).
  Notation "x 'o' y" := (app x y) (at level 35, right associativity).
  Notation "x * y" := (app x y) (at level 40, left associativity).
  Notation "x || y" := (join x y) (at level 50, left associativity).

  Let x := var 0.
  Let y := var 1.
  Let z := var 2.

  Definition TOP' := error.
  Definition S' := \x,\y,\z, x*z*(y*z).
  Definition K' := \x,\y, x.
  Definition I' := \x, x.
  Definition B' := \x,\y,\z, x*(y*z).
  Definition C' := \x,\y,\z, x*z*y.
  Definition Y' := \x, (\y, x*(y*y)) * (\y, x*(y*y)).
  Definition V' := Y' * \x,\y, I' || x o y.
  Definition div' := Y' * \x, x * TOP'.

  Definition Y := encode Y'.
  Definition V := encode V'.
  Definition div := encode div'.
End combinators.
