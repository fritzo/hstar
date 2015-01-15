(** * Types as closures *)

Require Import Coq.Classes.Morphisms.
Require Export Constructor.
Open Scope code_scope.

(** ** Properties of types *)

Definition closure {Var : Set} (a : Code Var) := I [= a /\ a o a == a.
Definition fixes {Var : Set} (a : Code Var) (x : Code Var) := a * x == x.
Notation "x :: a" := (fixes a x) : code_scope.

Definition inhabitants {Var : Set}
  (a : Code Var) (a_fixes : Code Var -> Prop) : Prop :=
  forall x, fixes a x <-> exists x', x == x' /\ a_fixes x'.

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

Instance inhabitants_proper_eq (Var : Set) :
  Proper (code_eq ==> (code_eq ==> iff) ==> iff) (@inhabitants Var).
Proof.
  intros a a' aa' f f' ff'.
  unfold inhabitants, fixes; simpl_relation; repeat (split; intros); auto.
Admitted.

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
  (* TODO this requires a least-fixed-point argument *)
Admitted.
Hint Rewrite semi_nondecreasing.

Lemma semi_closure {Var : Set} : closure (semi : Code Var).
Proof.
  split; [apply semi_nondecreasing | apply semi_idempotent].
Qed.

Lemma semi_inhab_bot (Var : Set) : BOT :: (semi : Code Var).
Proof.
Admitted.

Lemma semi_inhab_i (Var : Set) : I :: (semi : Code Var).
Proof.
  (* TODO this requires a least-fixed-point argument *)
Admitted.

Lemma semi_inhab_top (Var : Set) : TOP :: (semi : Code Var).
Proof.
Admitted.

Inductive semi_fixes {Var : Set} : Code Var -> Prop :=
  | semi_fixes_eq x y : x == y -> semi_fixes x -> semi_fixes y
  | semi_fixes_bot : semi_fixes BOT
  | semi_fixes_i : semi_fixes I
  | semi_fixes_top : semi_fixes TOP.
Hint Constructors semi_fixes.

Instance semi_fixes_proper (Var : Set) :
  Proper (code_eq ==> iff) (@semi_fixes Var).
Proof.
  intros x y xy; split; [idtac | apply symmetry in xy];
  intro H; induction H; eauto.
Qed.

Theorem semi_sound (Var : Set) (x : Code Var) :
  x :: semi -> semi_fixes x.
Proof.
  intros H; unfold fixes in H.
  (* TODO this requires a Bohm-tree argument *)
Admitted.

Theorem semi_inhab (Var : Set) (x : Code Var) : x :: semi <-> semi_fixes x.
Proof.
  split.
    apply semi_sound.
  intro H; induction H.
  rewrite <- H; auto.
  apply semi_inhab_bot.
  apply semi_inhab_i.
  apply semi_inhab_top.
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
Admitted.

Lemma boool_inhab_k (Var : Set) : K :: (boool : Code Var).
Proof.
Admitted.

Lemma boool_inhab_f (Var : Set) : K * I :: (boool : Code Var).
Proof.
Admitted.

Lemma boool_inhab_j (Var : Set) : J :: (boool : Code Var).
Proof.
Admitted.

Lemma boool_inhab_top (Var : Set) : TOP :: (boool : Code Var).
Proof.
Admitted.

Inductive boool_fixes {Var : Set} : Code Var -> Prop :=
  | boool_fixes_eq x y : x == y -> boool_fixes x -> boool_fixes y
  | boool_fixes_bot : boool_fixes BOT
  | boool_fixes_k : boool_fixes K
  | boool_fixes_f : boool_fixes (K * I)
  | boool_fixes_j : boool_fixes J
  | boool_fixes_top : boool_fixes TOP.
Hint Constructors boool_fixes.

Instance boool_fixes_proper (Var : Set) :
  Proper (code_eq ==> iff) (@boool_fixes Var).
Proof.
  intros x y xy; split; [idtac | apply symmetry in xy];
  intro H; induction H; eauto.
Qed.

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
