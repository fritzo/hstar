(** * Types as closures *)

Require Export Constructor.
Open Scope code_scope.

(** ** Properties of types *)

Definition closure {Var : Set} (a : Code Var) := I [= a /\ a o a == a.
Definition fixes {Var : Set} (a : Code Var) (x : Code Var) := a*x == x.
Notation "x :: a" := (fixes a x) : code_scope.

(** ** Atomic types *)

Lemma I_closure {Var : Set} : closure (I : Code Var).
Proof.
  unfold closure; split.
  apply code_le_refl.
  eta_expand; beta_reduce; auto.
Qed.

Theorem I_inhab (Var : Set) (x : Code Var) : x :: I <-> True.
Proof.
  unfold fixes.
  beta_reduce; firstorder.
Qed.

Lemma V_closure (Var : Set) : closure (V : Code Var).
Proof.
  unfold closure.
  split.
  (* TODO adapt Y_fix, eta, beta tactics from Points to Codes.
    unfold V; rewrite Y_fix; rewrite Y_fix; fold V.
    freeze V in (compute; eta_expand as f; eta_expand as x; beta_reduce).
    apply LESS_trans with (x || f * x); monotonicity; auto.
  TODO
  *)
Admitted.

Theorem V_inhab (Var : Set) (x : Code Var) : x :: V <-> closure x.
Proof.
  unfold fixes; unfold closure.
  split.
    intros Hfix; rewrite <- Hfix; clear Hfix.
    split.
  (* TODO *)
Admitted.

Corollary fixes_V_V (Var : Set) : fixes V (V : Code Var).
Proof.
  apply V_inhab.
  apply V_closure.
Qed.

Section semi.
  Variable Var : Set.
  Let a := make_var Var 0.
  Let a' := make_var Var 1.
  Definition Semi := close (\\a,a'; a --> a').
End semi.
Definition semi {Var : Set} := Semi Var.

Lemma semi_closure (Var : Set) : closure (semi : Code Var).
Proof.
  (* TODO *)
Admitted.

Theorem semi_inhab (Var : Set) (x : Code Var) : x :: semi <->
  x == BOT \/
  x == I \/
  x == TOP.
Proof.
  split.
  (* TODO *)
Admitted.

Section boool.
  Variable Var : Set.
  Let a := make_var Var 0.
  Let a' := make_var Var 1.
  Definition Boool := close (\\a,a'; a --> a --> a').
End boool.
Definition boool {Var : Set} := Boool Var.

Lemma boool_closure (Var : Set) : closure (boool : Code Var).
Proof.
  (* TODO *)
Admitted.

Theorem boool_inhab (Var : Set) (x : Code Var) : x :: boool <->
  x == BOT \/
  x == K \/
  x == K * I \/
  x == J \/
  x == TOP.
Proof.
  split.
  (* TODO *)
Admitted.
