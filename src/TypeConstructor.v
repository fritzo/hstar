(** * A constructor for polymorphic types *)

Require Import Coq.Logic.Decidable.
Require Import Coq.Program.Basics.
Require Import Coq.Program.Equality.
Require Import Coq.Setoids.Setoid.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Export InformationOrdering.
Require Import Nontermination.
Require Import LeastFixedPoint.
Require Import BohmTrees.
Open Scope code_scope.

(* ------------------------------------------------------------------------ *)
(** ** Components for Bohm-out moves *)

Section pair.
  Context {Var : Set}.
  Let x := make_var Var 0.
  Let y := make_var Var 1.
  Let f := make_var Var 2.
  Definition pair := Eval compute in close_var (\x,\y,\f, f * x * y).
End pair.
Notation "<< x , y >>" := (pair * x * y)%code : code_scope.

Definition is_pair {Var : Set} (x : Code Var) := x == <<x * K, x * (K * I)>>.
Lemma pair_is_pair (Var : Set) (x y : Code Var) : is_pair <<x, y>>.
Proof.
  hnf; unfold pair; beta_reduce; auto.
Qed.

Lemma pair_extensionality (Var : Set) (x y x' y' : Code Var) :
  <<x, y>> [= <<x', y'>> <-> x [= x' /\ y [= y'.
Proof.
  unfold pair; beta_simpl; split.
    intro H; split.
      apply (code_le_ap_left _ _ _ K) in H; beta_simpl in H; auto.
    apply (code_le_ap_left _ _ _ (K*I)) in H; beta_simpl in H; auto.
  intros [Hx Hy]; auto.
Qed.

Section raise.
  Context {Var : Set}.
  Let x := make_var Var 3.
  Let y := make_var Var 4.

  Definition raise := Eval compute in close_var (\x, \y, x).
  Definition lower := Eval compute in close_var (\x, x * TOP).

  Definition pull := Eval compute in close_var (\x, \y, x || div * y).
  Definition push := Eval compute in close_var (\x, x * BOT).

  Lemma lower_raise : lower o raise == I.
  Proof.
    unfold lower, raise; beta_eta.
  Qed.

  Lemma push_pull : push o pull == I.
  Proof.
    unfold push, pull; fold (@div Var); eta_expand as z; beta_simpl.
    symmetry; apply code_le_eq_j.
    rewrite div_bot; auto.
  Qed.
End raise.

Section exp.
  Context {Var : Set}.
  Let a := make_var Var 0.
  Let b := make_var Var 1.
  Let f := make_var Var 2.
  Definition exp := Eval compute in close_var (\a, \b, \f, b o f o a).
End exp.
Notation "x --> y" := (exp * x * y)%code : code_scope.

Lemma exp_i_i (Var : Set) : I --> I == (I : Code Var).
Proof.
  unfold exp; beta_eta.
Qed.

Section compose.
  Context {Var : Set}.
  Let s := make_var Var 0.
  Let a := make_var Var 1.
  Let a' := make_var Var 2.
  Let b := make_var Var 3.
  Let b' := make_var Var 4.

  Definition compose := Eval compute in close_var
    (\s, s*\a,\a', s*\b,\b', <<a o b, b' o a'>>).

  Definition conjugate := Eval compute in close_var
    (\s, s*\a,\a', s*\b,\b', <<a' --> b, a --> b'>>).
End compose.

Lemma compose_pair_le (Var : Set) (s1 r1 s2 r2 : Code Var) :
  <<s1 o s2, r2 o r1>> [= compose * (<<s1, r1>> || <<s2, r2>>).
Proof.
  unfold compose; beta_reduce; unfold pair; beta_simpl.
  rewrite pi_j_left, pi_j_right; reflexivity.
Qed.

Lemma conjugate_pair_le (Var : Set) (s1 r1 s2 r2 : Code Var) :
  <<r1 --> s2, s1 --> r2>> [= conjugate * (<<s1, r1>> || <<s2, r2>>).
Proof.
  unfold conjugate; beta_reduce; unfold pair; beta_simpl.
  rewrite pi_j_left, pi_j_right.
  unfold exp; code_simpl; reflexivity.
Qed.

(* ------------------------------------------------------------------------ *)
(** ** A constructive definition of [A] *)

Definition A_step {Var : Set} : Code Var
  := K * (<<I, I>> || <<raise, lower>> || <<pull, push>>)
    || (compose || conjugate).

Definition A {Var : Set} : Code Var := Eval compute in Y * A_step.

Lemma A_simpl (Var : Set) : (A : Code Var) == Y * A_step.
Proof.
  (freeze code_eq in compute); auto.
Qed.

Ltac A_simpl := rewrite A_simpl; unfold A_step.

(** We will make much use of the following theorems *)

Theorem A_fixes (Var : Set) (f x : Code Var) :
  (forall s r : Code Var, r o s [= I -> f * s * r * x [= x) ->
  A * f * x [= x.
Proof.
  intro H.
  (* TODO use a join argument: A = Join ys and forall y in ys, y f x [= x *)
Admitted.

Lemma A_exp_top (Var : Set) : A * exp * TOP == (TOP : Code Var).
Proof.
  split; auto.
  A_simpl; unfold exp, pair; rewrite code_eq_y; do 3 rewrite pi_j_left.
  eta_expand as x; beta_simpl; auto.
Qed.

(** We define some moves for Bohm-out arguments below. *)

Lemma A_move_i_i (Var : Set) : <<I, I>> [= (A : Code Var).
Proof.
  A_simpl;
  rewrite code_eq_y, pi_j_left, beta_k, pi_j_left, pi_j_left;
  reflexivity.
Qed.

Lemma A_move_raise_lower (Var : Set) : <<raise, lower>> [= (A : Code Var).
Proof.
  A_simpl;
  rewrite code_eq_y, pi_j_left, beta_k, pi_j_left, pi_j_right;
  reflexivity.
Qed.

Lemma A_move_pull_push (Var : Set) : <<pull, push>> [= (A : Code Var).
Proof.
  A_simpl; rewrite code_eq_y, pi_j_left, beta_k, pi_j_right;
  reflexivity.
Qed.

Lemma A_move_compose (Var : Set) (s1 r1 s2 r2 : Code Var) :
  <<s1, r1>> [= A -> <<s2, r2>> [= A -> <<s1 o s2, r2 o r1>> [= A.
Proof.
  rewrite A_simpl at 3; rewrite code_eq_y; rewrite <- A_simpl.
  unfold A_step; rewrite pi_j_right, pi_j_left.
  intros H1 H2.
  assert (<<s1, r1>> || <<s2, r2>> [= A) as H; auto; rewrite <- H.
  apply compose_pair_le.
Qed.

Lemma A_move_conjugate (Var : Set) (s1 r1 s2 r2 : Code Var) :
  <<s1, r1>> [= A -> <<s2, r2>> [= A -> <<r1 --> s2, s1 --> r2>> [= A.
Proof.
  rewrite A_simpl at 3; rewrite code_eq_y; rewrite <- A_simpl.
  unfold A_step; rewrite pi_j_right, pi_j_right.
  intros H1 H2.
  assert (<<s1, r1>> || <<s2, r2>> [= A) as H; auto; rewrite <- H.
  apply conjugate_pair_le.
Qed.


(* TODO use BohmTrees lemmas instead of this *)
Lemma conv_bt_witness (x : ClosedCode) :
  code_conv x -> exists k1 k2 b, K ^ k1 * (K ^ k2 o (C * I * BOT) ^ b) [= x.
Proof.
  intro H; rewrite conv_closed in H; destruct H as [y [xy yt]].
  apply weaken_probe in xy; apply weaken_pi in yt.
  dependent induction yt; eauto.
  - admit.
  - admit.
Qed.

Local Ltac move_i_i := rewrite <- A_move_i_i.
Local Ltac move_raise_lower := rewrite <- A_move_raise_lower.
Local Ltac move_pull_push := rewrite <- A_move_pull_push.

Require Import Coq.Classes.Equivalence.
Require Import Coq.Classes.SetoidTactics.

Theorem A_repairs_pair (i : ClosedCode) :
  ~ i [= BOT -> exists s r, <<s, r>> [= A /\ I [= r o i o s.
Proof.
  intro H; apply conv_nle_bot in H.
  apply conv_bt_witness in H; destruct H as [k1 [k2 [b H]]].
  setoid_rewrite <- H; clear H i.
  induction k1.
  - (* case: correct head variable *)
    induction k2; induction b.
    (* TODO consider the three cases k2=b, k2<b, k2>b *)
    + exists I, I; move_i_i; unfold exp, pair; code_simpl; auto.
    + destruct IHb as [s [r [Ha Hi]]]; code_simpl in Hi.
      exists (s o raise), (lower o r); split.
        apply A_move_compose; [assumption | apply A_move_raise_lower].
      simpl; unfold raise, lower; code_simpl.
      eta_expand as f; simpl; unfold raise, lower; code_simpl.
      admit.
    + destruct IHk2 as [s [r [Ha Hi]]]; code_simpl in Hi.
      admit.
    + admit.
  - (* case: incorrect head variable *)
    simpl.
    exists raise, lower; split; [apply A_move_raise_lower|].
    code_simpl.
    admit.
Qed.

Corollary A_repairs' (i : ClosedCode) : ~ i [= BOT -> I [= A * exp * i.
Proof.
  intro H; apply A_repairs_pair in H; destruct H as [s [r [Ha Hi]]].
  rewrite <- Ha; unfold pair, exp; code_simpl.
  assumption.
Qed.

(* TODO the following two theorems need stronger induction hypotheses,
   of higher type *)

Theorem A_repairs (i : ClosedCode) : ~ i [= BOT -> I [= A * exp * i.
Proof.
  repeat rewrite <- decompile_le.
  do 2 rewrite decompile_app; freeze A in freeze exp in simpl.
  set (i' := decompile i); subst.
  intro H; apply nle_normal_witness in H; destruct H as [n [Hn [ni nb]]].
  rewrite <- ni; clear i i' ni; revert nb.
  induction Hn; intro Hnle.
  - rewrite <- compile_le; freeze A in freeze exp in simpl.
    repeat rewrite compile_decompile.
    rewrite A_exp_top; auto.
  - assert ((BOT [= (BOT : Term Var))%term); [reflexivity | contradiction].
  - rewrite term_le_join in Hnle.
    apply not_and in Hnle; auto.
    destruct Hnle as [Hx | Hy];
    [rewrite <- term_le_join_left | rewrite <- term_le_join_right]; auto.
  - admit.  (* TODO use [pconv] instead of [conv] *)
  (* the last three cases require shifting down and up type. *)
  - admit.  (* TODO prove a lemma about [inert] terms *)
  - admit.
  - admit.
Qed.

Theorem A_raises (i : ClosedCode) : ~ i [= I -> TOP [= A * exp * i.
Proof.
  repeat rewrite <- decompile_le.
  do 2 rewrite decompile_app; freeze A in freeze exp in simpl.
  set (i' := decompile i); subst.
  intro H; apply nle_normal_witness in H; destruct H as [n [Hn [ni nb]]].
  rewrite <- ni; clear i i' ni; revert nb.
  induction Hn; intro Hnle.
  - rewrite <- compile_le; freeze A in freeze exp in simpl.
    repeat rewrite compile_decompile.
    rewrite A_exp_top; auto.
  - assert ((BOT [= (DeBruijn.I : Term Var))%term);
      [term_to_code | contradiction].
  - rewrite term_le_join in Hnle.
    apply not_and in Hnle; auto.
    destruct Hnle as [Hx | Hy];
    [rewrite <- term_le_join_left | rewrite <- term_le_join_right]; auto.
  - admit.  (* TODO use [pconv] instead of [conv] *)
  (* the last three cases require shifting down and up type. *)
  - admit.  (* TODO prove a lemma about [inert] terms *)
  - admit.
  - admit.
Qed.

(** To generalize to probability,
    we need two parametrized relations [code_ple] and [code_pnle] meaning
    that at least [p] of the time, [code_le] or [~ code_le] holds.
    Note that [code_pnle] is stronger than
    "it is false that [code_le] holds at least p of the time".
    *)

Definition code_ple (p : dyadic) {Var : Set} (x y : Code Var) :=
  x [= dyadic_sub x y p.

(* FIXME Is this right? *)
Definition code_pnle (p : dyadic) {Var : Set} (x y : Code Var) :=
  ~ x || y [= dyadic_sub x y p.

Theorem A_repairs_prob (i : ClosedCode) (p : dyadic) :
  code_pnle p i BOT -> code_ple p I (A * exp * i).
Proof.
  admit.
Qed.

Theorem A_raises_prob (i : ClosedCode) (p : dyadic) :
  ~ i [= (dyadic_sub BOT I p) -> dyadic_sub BOT TOP p [= A * exp * i.
Proof.
  admit.
Qed.

Notation "\\ x , y ; z" := (A * \x, \y, z)%code : code_scope.

Section A_example.
  Variable Var : Set.
  Let a := make_var Var 0.
  Let a' := make_var Var 1.
  Let A_example : Code Var := close_var (\\a,a'; a --> a').
End A_example.
