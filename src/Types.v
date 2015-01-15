(** * Types as closures *)

Require Import Coq.Classes.Morphisms.
Require Export Constructor.
Open Scope code_scope.

(** ** Properties of types *)

Definition closure {Var : Set} (a : Code Var) := I [= a /\ a o a == a.
Definition fixes {Var : Set} (a : Code Var) (x : Code Var) := a * x == x.
Notation "x :: a" := (fixes a x) : code_scope.

Instance closure_proper_eq (Var : Set) :
  Proper (code_eq ==> iff) (@closure Var).
Proof.
  simpl_relation; unfold closure; split; intros [Hn Hi]; split;
  (rewrite -> H || rewrite <- H); auto.
Qed.

Instance fixes_proper_eq (Var : Set) :
  Proper (code_eq ==> code_eq ==> iff) (@fixes Var).
Proof.
  unfold fixes; intros a a' Ha x x' Hx.
  rewrite Ha; rewrite Hx; firstorder.
Qed.

Lemma nondecreasing_idempotent (Var : Set) (a : Code Var) :
 I [= a -> a o a [= a -> a o a == a.
Proof.
  intros Hi Hr; split; auto.
  rewrite <- Hi at 2; beta_eta.
Qed.
Hint Resolve nondecreasing_idempotent.

Lemma closure_weak (Var : Set) (a : Code Var) :
 I [= a -> a o a [= a -> closure a.
Proof.
  unfold closure; intros; split; auto.
Qed.

(** ** Atomic types *)

(** [I] is the largest type. *)

Lemma I_nondecreasing (Var : Set) : I [= (I : Code Var).
Proof. auto. Qed.

Lemma I_idempotent (Var : Set) : I o I == (I : Code Var).
Proof. beta_eta. Qed.
Hint Rewrite I_nondecreasing.

Lemma I_closure {Var : Set} : closure (I : Code Var).
Proof.
  split; [apply I_nondecreasing | apply I_idempotent].
Qed.

Theorem I_inhab (Var : Set) (x : Code Var) : x :: I <-> True.
Proof.
  unfold fixes; beta_reduce; firstorder.
Qed.

(** [V] is the type of all types *)

Lemma V_nondecreasing (Var : Set) : I [= (V : Code Var).
Proof.
  eta_expand as a.
  rewrite beta_v; rewrite pi_j_right.
  rewrite beta_v; rewrite pi_j_left.
  beta_eta.
Qed.

Lemma V_idempotent (Var : Set) : V o V == (V : Code Var).
Proof.
  apply nondecreasing_idempotent.
    apply V_nondecreasing.
    eta_expand as a; rewrite beta_b.
Admitted.
Hint Rewrite V_nondecreasing.

Lemma V_closure {Var : Set} : closure (V : Code Var).
Proof.
  split; [apply V_nondecreasing | apply V_idempotent].
Qed.

Lemma V_sound (Var : Set) (x : Code Var) : x :: V -> closure x.
Proof.
  unfold fixes, closure.
  intros Hfix.
  assert (I [= x).
    rewrite <- Hfix; rewrite beta_v; auto.
  split; auto.
  rewrite <- Hfix at 3; rewrite beta_v; rewrite Hfix.
  split; auto.
  apply code_le_j_ub; auto.
  rewrite <- I_idempotent.
  monotonicity; auto.
Qed.

Lemma V_complete (Var : Set) (x : Code Var) : closure x -> x :: V.
Proof.
  unfold fixes, closure; intros [Hn Hi].
  (* TODO this requires a least fixed point lemma *)
Admitted.

Theorem V_inhab (Var : Set) (x : Code Var) : x :: V <-> closure x.
Proof.
  split; [apply V_sound | apply V_complete].
Qed.

Corollary fixes_V_V (Var : Set) : fixes V (V : Code Var).
Proof.
  apply V_inhab; apply V_closure.
Qed.

(** [semi] is Sierpinsky space, inhabited by [{BOT, I, TOP}]. *)

Section semi.
  Context {Var : Set}.
  Let a := make_var Var 0.
  Let a' := make_var Var 1.
  Definition semi := Eval compute in close (\\a,a'; a --> a').
End semi.

Lemma semi_nondecreasing (Var : Set) : I [= (semi : Code Var).
Proof.
  unfold semi.
  eta_expand as a.
  rewrite beta_y; rewrite pi_j_left.
  rewrite beta_j_ap.
  repeat rewrite pi_j_left.
  beta_simpl.
  beta_eta.
Qed.

Lemma semi_idempotent (Var : Set) : semi o semi == (semi : Code Var).
Proof.
  eta_expand as a; rewrite beta_b.
Admitted.
Hint Rewrite semi_nondecreasing.

Lemma semi_closure {Var : Set} : closure (semi : Code Var).
Proof.
  split; [apply semi_nondecreasing | apply semi_idempotent].
Qed.

Lemma semi_inhab_bot (Var : Set) : BOT :: (semi : Code Var).
Proof.
  unfold semi.
Admitted.

Lemma semi_inhab_i (Var : Set) : I :: (semi : Code Var).
Proof.
  unfold semi.
Admitted.

Lemma semi_inhab_top (Var : Set) : TOP :: (semi : Code Var).
Proof.
  unfold semi.
Admitted.

Theorem semi_sound (Var : Set) (x : Code Var) : x :: semi ->
  x == BOT \/
  x == I \/
  x == TOP.
Proof.
  intros H; unfold fixes in H.
Admitted.

Theorem semi_inhab (Var : Set) (x : Code Var) : x :: semi <->
  x == BOT \/
  x == I \/
  x == TOP.
Proof.
  split.
    apply semi_sound.
  intro H; destruct H as [Hb | [Hi | Ht]].
  rewrite Hb; apply semi_inhab_bot.
  rewrite Hi; apply semi_inhab_i.
  rewrite Ht; apply semi_inhab_top.
Qed.

(** [boool] is the set of ambiguous boolean values [K], [F], and [J].
    We will later define a stricter [bool] that raises [J] to [TOP],
    i.e., raising an error on ambiguous values. *)

Section boool.
  Context {Var : Set}.
  Let a := make_var Var 0.
  Let a' := make_var Var 1.
  Definition boool := Eval compute in close (\\a,a'; a --> a --> a').
End boool.

Lemma boool_nondecreasing (Var : Set) : I [= (boool : Code Var).
Proof.
  unfold boool.
  eta_expand as a.
  rewrite beta_y; rewrite pi_j_left.
  rewrite beta_j_ap.
  repeat rewrite pi_j_left.
  beta_simpl.
  beta_eta.
Qed.

Lemma boool_idempotent (Var : Set) : boool o boool == (boool : Code Var).
Proof.
  eta_expand as a; rewrite beta_b.
Admitted.
Hint Rewrite boool_nondecreasing.

Lemma boool_closure {Var : Set} : closure (boool : Code Var).
Proof.
  split; [apply boool_nondecreasing | apply boool_idempotent].
Qed.

Lemma boool_inhab_bot (Var : Set) : BOT :: (boool : Code Var).
Proof.
  unfold boool.
Admitted.

Lemma boool_inhab_k (Var : Set) : K :: (boool : Code Var).
Proof.
  unfold boool.
Admitted.

Lemma boool_inhab_f (Var : Set) : K * I :: (boool : Code Var).
Proof.
  unfold boool.
Admitted.

Lemma boool_inhab_j (Var : Set) : J :: (boool : Code Var).
Proof.
  unfold boool.
Admitted.

Lemma boool_inhab_top (Var : Set) : TOP :: (boool : Code Var).
Proof.
  unfold boool.
Admitted.

Theorem boool_sound (Var : Set) (x : Code Var) : x :: boool ->
  x == BOT \/
  x == K \/
  x == K * I \/
  x == J \/
  x == TOP.
Proof.
  intros H; unfold fixes in H.
Admitted.

Theorem boool_inhab (Var : Set) (x : Code Var) : x :: boool <->
  x == BOT \/
  x == K \/
  x == K * I \/
  x == J \/
  x == TOP.
Proof.
  split.
    apply boool_sound.
  intro H; destruct H as [Hb |[ Hk |[ Hf |[ Hj | Ht]]]].
  rewrite Hb; apply boool_inhab_bot.
  rewrite Hk; apply boool_inhab_k.
  rewrite Hf; apply boool_inhab_f.
  rewrite Hj; apply boool_inhab_j.
  rewrite Ht; apply boool_inhab_top.
Qed.
