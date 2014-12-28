(** * Translation [Ob <-> Lambda].

    This demonstrates a simple way to write combinators using lambda notation,
    but does not allow any direct reasoning about lambda Lambdas.
    The main trick is to embed inline-assembly-style Ob blocks
    in lambda Lambdas via a [OB] constructor.
    *)

Require Import ObAxioms.
Require Import EqNat.
Require Import Setoid.

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

  Fixpoint occurs (n : nat) (x : Lambda) : bool :=
    match x with
    | VAR m => beq_nat m n
    | ABS m y => andb (beq_nat m n) (occurs n y)
    | APP y z => orb (occurs n y) (occurs n z)
    | y => false
    end.

  (* Simple [I,K,S] abstraction *)
  Fixpoint abstract0 (n : nat) (x : Lambda) : Lambda :=
    match x with
    | VAR m => if beq_nat m n then [I] else [K] [*] x
    | ABS m y => if beq_nat m n then [K] [*] x else ABS m (abstract0 n y)
    | APP y z => [S] [*] (abstract0 n y) [*] (abstract0 n z)
    | _ => [K] [*] x
    end.

  (* Efficient [I,K,B,C,W,S,eta] abstraction *)
  Fixpoint abstract (n : nat) (x : Lambda) : Lambda :=
    match x with
    | VAR m => if beq_nat m n then [I] else [K] [*] x
    | ABS m y => if beq_nat m n then [K] [*] x else ABS m (abstract n y)
    | APP y z =>
        match occurs n y, occurs n z, z with
        | true, true, VAR _ => [W] [*] (abstract n y)
        | false, true, VAR _ => y
        | true, true, _ => [S] [*] (abstract n y) [*] (abstract n z)
        | true, false, _ => [C] [*] (abstract n y) [*] z
        | false, true, _ => [B] [*] y [*] (abstract n z)
        | false, false, _ => [K] [*] x
        end
    | _ => [K] [*] x
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

Delimit Scope Lambda_scope with Lambda.
Bind Scope Lambda_scope with Lambda.

(* Bind Scope is not retroactive, so: *)
Arguments encode _%Lambda.

Close Scope Ob_scope.
Open Scope Lambda_scope.
Open Scope Ob_scope.

Notation "x * y" := (APP x y)%Lambda
  (at level 40, left associativity) : Lambda_scope.
Notation "\ x , y" := (abs x y)%Lambda
  (at level 60, right associativity) : Lambda_scope.
Notation "x 'o' y" := ([B] * x * y)%Lambda
  (at level 30, right associativity) : Lambda_scope.
Notation "x || y" := ([J] * x * y)%Lambda
  (at level 50, left associativity) : Lambda_scope.
Notation "x (+) y" := ([R] * x * y)%Lambda
  (at level 45, no associativity) : Lambda_scope.

(** ** A standard library *)

Section Y.
  Let x := VAR 0.
  Let y := VAR 1.
  Definition Y := encode (\x, (\y, x*(y*y)) * (\y, x*(y*y))).
End Y.
Lemma Y_fix : forall f : Ob, Y*f = f*(Y*f).
Proof.
  intros. unfold Y. compute.
  rewrite S_beta at 1.
  rewrite C_beta at 1.
  rewrite B_beta at 1.
  rewrite W_beta at 1.
  rewrite I_beta at 1.
  rewrite <- S_beta at 1.
  auto.
Qed.

Lemma Y_lfp : forall f x, (forall y, y [= x -> f*y [= x) -> Y*f [= x.
Proof.
  intros f x H.
  (* TODO *)
Admitted.

Section V.
  Let x := VAR 0.
  Let y := VAR 1.
  Definition V_prefix := encode (\x,\y, [I] || y o (x * y)).
  Definition V := Y * V_prefix.
End V.
Lemma V_fix : forall f : Ob, f o (V*f) [= V*f.
Proof.
  intros f.
  unfold V; rewrite Y_fix at 2; fold V.
  freeze V in (compute; beta_reduce).
  unfold V_prefix.
  auto.
Qed.

Section div.
  Let x := VAR 0.
  Definition div_prefix := encode (\x, x * [TOP]).
  Definition div := Y * div_prefix.
End div.

Lemma div_BOT: div*BOT = BOT.
Proof.
  apply LESS_antisym.
    unfold div.
    admit. (* TODO *)
  auto.
Qed.
Hint Rewrite div_BOT.

Section exp.
  Let a := VAR 0.
  Let b := VAR 1.
  Let f := VAR 2.
  Definition exp := encode (\a, \b, \f, b o f o a).
End exp.
Notation "x --> y" := ([exp] * x * y)%Lambda
  (at level 55, right associativity) : Lambda_scope.
Lemma exp_I_I: exp * I * I = I.
Proof.
  compute; eta_expand; eta_expand; beta_reduce; auto.
Qed.
