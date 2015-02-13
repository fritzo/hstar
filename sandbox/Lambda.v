(** * Translation [Ob <-> Lambda].

    This demonstrates a simple way to write combinators using lambda notation,
    but does not allow any direct reasoning about lambda Lambdas.
    The main trick is to embed inline-assembly-style Ob blocks
    in lambda Lambdas via a [OB] constructor.
    *)

Require Import EqNat.
Require Import Setoid.
Require Import ObAxioms.
Require Import Notations.

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

  (* Simple [K,S] abstraction *)
  Fixpoint abstract0 (n : nat) (x : Lambda) : Lambda :=
    match x with
    | VAR m => if beq_nat m n then [S*K*K] else [K] [*] x
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

  Fixpoint compile (a : nat -> Lambda -> Lambda) (x : Lambda) : Lambda :=
    match x with
    | APP y z => APP (compile a y) (compile a z)
    | ABS n y => a n (compile a y)
    | y => y
    end.

  Fixpoint close (x : Lambda) : Ob :=
    match x with
    | OB y => y
    | APP y z => AP (close y) (close z)
    | _ => TOP
    end.

  Definition encode0 x := close (compile abstract0 x).
  Definition encode x := close (compile abstract x).
End Encode.

Notation "[ x ]" := (OB x) : Lambda_scope.

Delimit Scope Lambda_scope with Lambda.
Bind Scope Lambda_scope with Lambda.

(* Bind Scope is not retroactive, so : *)
(* Coq 8.4+
Arguments encode _%Lambda.
*)
(* Coq <8.4 *)
Arguments Scope encode [Lambda_scope].

Close Scope Ob_scope.
Open Scope Lambda_scope.
Open Scope Ob_scope.

Notation "x * y" := (APP x y)%Lambda : Lambda_scope.
Notation "\ x , y" := (abs x y)%Lambda : Lambda_scope.
Notation "x 'o' y" := ([B] * x * y)%Lambda : Lambda_scope.
Notation "x || y" := ([J] * x * y)%Lambda : Lambda_scope.
Notation "x (+) y" := ([R] * x * y)%Lambda : Lambda_scope.

Section I_def.
  Let x := VAR 0.
  Let y := VAR 1.
  Let z := VAR 2.

  Lemma I_def : I = encode0 (\x, x). beta_eta. Qed.
  Lemma F_def : F = encode0 (\x,\y, y). beta_eta. Qed.
  Lemma B_def : B = encode0 (\x,\y,\z, x * (y * z)). beta_eta. Qed.
  Lemma C_def : C = encode0 (\x,\y,\z, x * z * y). beta_eta. Qed.
  Lemma W_def : W = encode0 (\x,\y, x * y * y). beta_eta. Qed.
End I_def.

Lemma I_definable : definable I. rewrite I_def; compute; auto. Qed.
Lemma F_definable : definable F. rewrite F_def; compute; auto. Qed.
Lemma B_definable : definable B. rewrite B_def; compute; auto 100. Qed.
Lemma C_definable : definable C. rewrite C_def; compute; auto 100. Qed.
Lemma W_definable : definable W. rewrite W_def; compute; auto 100. Qed.

Hint Resolve I_definable F_definable B_definable C_definable W_definable.

(** ** A standard library *)

Section Omega.
  Let x := VAR 0.
  Definition Omega := encode ((\x, x*x) * (\x, x*x)).
End Omega.
Lemma Omega_diverges : code_conv Omega -> Empty_set.
Proof.
  compute; intros H.
  inversion H.
    admit. (* TODO *)
  admit. (* TODO *)
Admitted.

Lemma eq_Omega_BOT : Omega = BOT.
Proof.
  apply LESS_antisym.
    apply LESS_conv; intros f Hdef Hconv.
    inversion Hconv.
      admit. (* TODO *)
    admit. (* TODO *)
  auto.
Admitted.

Section Y.
  Let x := VAR 0.
  Let y := VAR 1.
  Definition Y := encode (\x, (\y, x*(y*y)) * (\y, x*(y*y))).
End Y.
Lemma Y_definable : definable Y. compute; auto. Qed.
Lemma Y_fix : forall f : Ob, Y*f = f*(Y*f).
Proof.
  intros; unfold Y; compute.
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
Lemma V_definable : definable V. compute; auto 100. Qed.
Lemma V_fix : forall f : Ob, f o (V*f) [= V*f.
Proof.
  intros f.
  unfold V; rewrite Y_fix at 2; fold V.
  freeze V in (compute; beta_reduce).
  unfold V_prefix.
  auto.
Qed.

Definition TOP_def := V * K.
Lemma TOP_TOP_def : TOP = TOP_def.
Proof.
  apply LESS_antisym.
    unfold TOP_def.
    apply LESS_conv; intros f Hconv.
    admit. (* TODO *)
  auto.
Qed.

Theorem TOP_definable : definable TOP.
Proof.
  rewrite TOP_TOP_def; compute; auto 100.
Qed.
Hint Resolve TOP_definable.

Section div.
  Let x := VAR 0.
  Definition div_prefix := encode (\x, x * [TOP]).
  Definition div := Y * div_prefix.
End div.

Lemma div_BOT : div*BOT = BOT.
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
Notation "x --> y" := ([exp] * x * y)%Lambda : Lambda_scope.
Lemma exp_I_I : exp * I * I = I.
Proof. beta_eta. Qed.
