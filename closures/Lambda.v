(** * Translation [Ob <-> Lambda].

    This demonstrates a simple way to write combinators using lambda notation,
    but does not allow any direct reasoning about lambda Lambdas.
    The main trick is to embed inline-assembly-style Ob blocks
    in lambda Lambdas via a [OB] constructor.
    *)

Require Import ObAxioms.
Require Import EqNat.

Open Scope Ob_scope.

Inductive Lambda : Set :=
| OB : Ob -> Lambda
| VAR : nat -> Lambda
| ABS : nat -> Lambda -> Lambda
| APP : Lambda -> Lambda -> Lambda.

Definition abs (x y : Lambda) : Lambda :=
  match x with
  | VAR n => ABS n y
  | z => OB TOP  (* HACK *)
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

Notation "[ x ]" := (OB x) : Lambda_scope.

Delimit Scope Lambda_Scope with Lambda.
Bind Scope Lambda_Scope with Lambda.

Open Scope Lambda_scope.
  Notation "x * y" := (APP x y)
    (at level 40, left associativity) : Lambda_scope.
  Notation "\ x , y" := (abs x y)
    (at level 60, right associativity) : Lambda_scope.
  Notation "x 'o' y" := ([B] * x * y)
    (at level 30, right associativity) : Lambda_scope.
  Notation "x || y" := ([J] * x * y)
      (at level 50, left associativity) : Lambda_scope.
  Notation "x (+) y" := ([R] * x * y)
    (at level 45, no associativity) : Lambda_scope.
Close Scope Lambda_scope.

(*
Notation "'x'" := (VAR 0) : Lambda_scope.
Notation "'y'" := (VAR 1) : Lambda_scope.
Notation "'z'" := (VAR 2) : Lambda_scope.
*)

Arguments Scope OB [Ob_scope].
Arguments Scope VAR [nat_scope].
Arguments Scope ABS [nat_scope Lambda_scope].
Arguments Scope APP [Lambda_scope Lambda_scope].
Arguments Scope abs [Lambda_scope Lambda_scope].
Arguments Scope encode [Lambda_scope].

(** ** A standard library *)

Section Y.
  Open Scope Lambda_scope.
  Let x := VAR 0.
  Let y := VAR 1.
  Definition Y := encode (\x, (\y, x*(y*y)) * (\y, x*(y*y))).
End Y.
Lemma Y_fix : forall f : Ob, Y*f = f*(Y*f).
Proof.
  intros. unfold Y. compute.
  (* TODO *)
Admitted.

Section V.
  Open Scope Lambda_scope.
  Let x := VAR 0.
  Let y := VAR 1.
  Definition V := encode ([Y] * \x,\y, [I] || x o y).
End V.
Lemma V_fix : forall f : Ob, f*(V*f) [= V*f.
Proof.
  intros. unfold V. compute.
  firstorder.
  (* TODO *)
Admitted.

Section div.
  Local Open Scope Lambda_scope.
  Let x := VAR 0.
  Definition div := encode ([Y] * \x, x * [TOP]).
End div.

Section exp.
  Local Open Scope Lambda_scope.
  Let a := VAR 0.
  Let b := VAR 0.
  Let f := VAR 0.
  Definition exp := encode (\a, \b, \f, b o f o a).
End exp.
Open Scope Lambda_scope.
  Notation "x --> y" := ([exp] * x * y)
    (at level 55, right associativity) : Lambda_scope.
Close Scope Lambda_scope.
Lemma exp_I_I: exp * I * I = I.
Proof.
  apply extensionality.
  intro x.
  compute.
  (* TODO: Ltac beta_normalize *)
Admitted.
