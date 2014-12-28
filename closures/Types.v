(** * Types as closures *)

Require Import ObAxioms.
Require Import Lambda.
Require Import Constructor.

Open Scope Ob_scope.

(** ** Properties of types *)

Definition closure (a : Ob) := I [= a /\ a o a = a.
Definition fixes (a : Ob) (x : Ob) := a*x = x.
Notation "x :: a" := (fixes a x) : Ob_scope.

(** ** Atomic types *)

Lemma I_closure: closure I.
Proof.
  unfold closure; split.
  apply LESS_refl.
  eta_expand; beta_reduce; auto.
Qed.

Theorem I_inhab (x : Ob) : x :: I <-> True.
Proof.
  unfold fixes.
  beta_reduce; firstorder.
Qed.

Lemma V_closure: closure V.
Proof.
  unfold closure.
  split.
    unfold V; rewrite Y_fix; rewrite Y_fix; fold V.
    freeze V in (compute; eta_expand as f; eta_expand as x; beta_reduce).
    apply LESS_trans with (x || f * x); monotonicity; auto.
  (* TODO *)
Admitted.

Theorem V_inhab (x : Ob) : x :: V <-> closure x.
Proof.
  unfold fixes. unfold closure.
  split.
    intros Hfix; rewrite <- Hfix; clear Hfix.
    split.
  (* TODO *)
Admitted.

Corollary fixes_V_V: fixes V V.
Proof.
  apply V_inhab.
  apply V_closure.
Qed.

Section semi.
  Let a := VAR 0.
  Let a' := VAR 1.
  Definition semi := encode (\\a,a'; a --> a').
End semi.

Lemma semi_closure: closure semi.
Proof.
  (* TODO *)
Admitted.

Theorem semi_inhab (x : Ob) : x :: semi <->
  x = BOT \/
  x = I \/
  x = TOP.
Proof.
  split.
  (* TODO *)
Admitted.

Section boool.
  Let a := VAR 0.
  Let a' := VAR 1.
  Definition boool := encode (\\a,a'; a --> a --> a').
End boool.

Lemma boool_closure: closure semi.
Proof.
  (* TODO *)
Admitted.

Theorem boool_inhab (x : Ob) : x :: boool <->
  x = BOT \/
  x = K \/
  x = F \/
  x = J \/
  x = TOP.
Proof.
  split.
  (* TODO *)
Admitted.
