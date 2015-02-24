(** * A constructor for polymorphic types *)

Require Import Omega.
Require Import Coq.Logic.Decidable.
Require Import Coq.Program.Basics.
Require Import Coq.Program.Equality.
Require Import Coq.Setoids.Setoid.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Arith.Compare_dec.
Require Import Coq.Arith.Plus.
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
Notation "[ x , y ]" := (pair * x * y)%code : code_scope.
Notation "[ x ]" := (C * I * x)%code : code_scope.

Lemma pair_extensionality (Var : Set) (x y x' y' : Code Var) :
  [x, y] [= [x', y'] <-> x [= x' /\ y [= y'.
Proof.
  unfold pair; beta_simpl; split.
    intro H; split.
      apply (code_le_ap_left _ _ _ K) in H; beta_simpl in H; auto.
    apply (code_le_ap_left _ _ _ (K*I)) in H; beta_simpl in H; auto.
  intros [Hx Hy]; auto.
Qed.

Section raise.
  Context {Var : Set}.

  Definition raise : Code Var := K.
  Definition lower : Code Var := [TOP].

  Definition pull : Code Var := K || K * div.
  Definition push : Code Var := [BOT].
End raise.

Lemma lower_raise (Var : Set) (x : Code Var) : lower * (raise * x) == x.
Proof.
  unfold lower, raise; beta_simpl; reflexivity.
Qed.

Lemma push_pull (Var : Set) (x : Code Var) : push * (pull * x) == x.
Proof.
  unfold push, pull; code_simpl; reflexivity.
Qed.

Lemma lower_pull (Var : Set) (x : Code Var) : lower * (pull * x) == TOP.
Proof.
  unfold lower, pull; code_simpl;
  rewrite code_eq_div; code_simpl; reflexivity.
Qed.

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
    (\s, s*\a,\a', s*\b,\b', [a o b, b' o a']).

  Definition conjugate := Eval compute in close_var
    (\s, s*\a,\a', s*\b,\b', [a' --> b, a --> b']).
End compose.

Lemma compose_pair_le (Var : Set) (s1 r1 s2 r2 : Code Var) :
  [s1 o s2, r2 o r1] [= compose * ([s1, r1] || [s2, r2]).
Proof.
  unfold compose, pair; beta_reduce.
  rewrite pi_j_left, pi_j_right; reflexivity.
Qed.

Lemma conjugate_pair_le (Var : Set) (s1 r1 s2 r2 : Code Var) :
  [r1 --> s2, s1 --> r2] [= conjugate * ([s1, r1] || [s2, r2]).
Proof.
  unfold conjugate, pair; beta_reduce.
  rewrite pi_j_left, pi_j_right.
  unfold exp; code_simpl; reflexivity.
Qed.

(* ------------------------------------------------------------------------ *)
(** ** A constructive definition of [A] *)

Definition A_step {Var : Set} : Code Var
  := K * ([I, I] || [raise, lower] || [pull, push])
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

(* ------------------------------------------------------------------------ *)
(** ** Using the Bohm-out method through [A] *)

Lemma A_move_i_i (Var : Set) : [I, I] [= (A : Code Var).
Proof.
  A_simpl;
  rewrite code_eq_y, pi_j_left, beta_k, pi_j_left, pi_j_left;
  reflexivity.
Qed.

Lemma A_move_raise_lower (Var : Set) : [raise, lower] [= (A : Code Var).
Proof.
  A_simpl;
  rewrite code_eq_y, pi_j_left, beta_k, pi_j_left, pi_j_right;
  reflexivity.
Qed.

Lemma A_move_pull_push (Var : Set) : [pull, push] [= (A : Code Var).
Proof.
  A_simpl; rewrite code_eq_y, pi_j_left, beta_k, pi_j_right;
  reflexivity.
Qed.

Lemma A_move_compose (Var : Set) (s1 r1 s2 r2 : Code Var) :
  [s1, r1] [= A -> [s2, r2] [= A -> [s1 o s2, r2 o r1] [= A.
Proof.
  rewrite A_simpl at 3; rewrite code_eq_y; rewrite <- A_simpl.
  unfold A_step; rewrite pi_j_right, pi_j_left.
  intros H1 H2.
  assert ([s1, r1] || [s2, r2] [= A) as H; auto; rewrite <- H.
  apply compose_pair_le.
Qed.

Lemma A_move_conjugate (Var : Set) (s1 r1 s2 r2 : Code Var) :
  [s1, r1] [= A -> [s2, r2] [= A -> [r1 --> s2, s1 --> r2] [= A.
Proof.
  rewrite A_simpl at 3; rewrite code_eq_y; rewrite <- A_simpl.
  unfold A_step; rewrite pi_j_right, pi_j_right.
  intros H1 H2.
  assert ([s1, r1] || [s2, r2] [= A) as H; auto; rewrite <- H.
  apply conjugate_pair_le.
Qed.

Lemma A_move_raise_lower_n (Var : Set) (n : nat) :
  [raise^n, lower^n] [= (A : Code Var).
Proof.
  induction n; simpl.
  - apply A_move_i_i.
  - rewrite power_commute_1'; apply A_move_compose; auto.
    apply A_move_raise_lower.
Qed.

Lemma A_move_pull_push_n (Var : Set) (n : nat) :
  [pull^n, push^n] [= (A : Code Var).
Proof.
  induction n; simpl.
  - apply A_move_i_i.
  - rewrite power_commute_1'; apply A_move_compose; auto.
    apply A_move_pull_push.
Qed.

Hint Resolve 
  A_move_i_i A_move_raise_lower A_move_pull_push
  A_move_compose A_move_conjugate
  A_move_raise_lower_n A_move_pull_push_n
  : A_moves.

Lemma lower_top (n : nat) : lower^n * TOP == (TOP : ClosedCode).
Proof.
  induction n; simpl; code_simpl; auto.
  rewrite IHn; unfold lower; code_simpl; auto.
Qed.

Lemma push_top (n : nat) : push^n * TOP == (TOP : ClosedCode).
Proof.
  induction n; simpl; code_simpl; auto.
  rewrite IHn; unfold push; code_simpl; auto.
Qed.

Lemma lower_k (n : nat) (x : ClosedCode) : lower^n * (K^n * x) == x.
Proof.
  revert x; induction n; intro x; simpl; code_simpl; auto.
  setoid_rewrite power_commute_1 at 2.
  rewrite IHn; unfold lower; beta_simpl; reflexivity.
Qed.

Lemma push_k (n : nat) (x : ClosedCode) : push^n * (K^n * x) == x.
Proof.
  revert x; induction n; intro x; simpl; code_simpl; auto.
  setoid_rewrite power_commute_1 at 2.
  rewrite IHn; unfold push; beta_simpl; reflexivity.
Qed.

Lemma raise_c_i_bot (n : nat) (x : ClosedCode) :
  [BOT]^n * (raise^n * x) == x.
Proof.
  revert x; induction n; intro x; simpl; code_simpl; auto.
  rewrite power_commute_1, IHn; unfold raise; beta_simpl; reflexivity.
Qed.

Lemma pull_c_i_bot (n : nat) (x : ClosedCode) :
  [BOT]^n * (pull^n * x) == x.
Proof.
  revert x; induction n; intro x; simpl; code_simpl; auto.
  rewrite power_commute_1, IHn; unfold pull; code_simpl; reflexivity.
Qed.


Ltac bohm_out :=
  split; code_simpl; auto with A_moves;
  eta_expand; code_simpl.

Lemma bohm_out_repair (b : nat) :
  exists s r : ClosedCode, [s, r] [= A /\ I [= r o K ^ b o [BOT] ^ b o s.
Proof.
  exists (raise^b), (lower^b); bohm_out.
  rewrite raise_c_i_bot, lower_k; reflexivity.
Qed.

Lemma bohm_out_too_many_args (k d : nat) :
  exists s r : ClosedCode, [s, r] [= A /\
  TOP [= r o K ^ k o [BOT] ^ (1 + k + d) o s.
Proof.
  exists (raise^(1+d+k) o pull), (push o lower^(1+d+k)); bohm_out.
  replace (1 + k + d) with (1 + d + k) by omega.
  rewrite power_add, raise_c_i_bot, lower_k.
  replace (1 + d) with (d + 1) by omega.
  rewrite power_add; code_simpl.
  rewrite lower_pull, lower_top.
  unfold push; code_simpl; auto.
Qed.

Lemma bohm_out_too_few_args (b d : nat) :
  exists s r : ClosedCode, [s, r] [= A /\
  TOP [= r o K ^ (1 + d + b) o [BOT] ^ b o s.
Proof.
  exists (pull^(1+d+b) o raise), (lower o push^(1+d+b)); bohm_out.
  rewrite push_k; code_simpl.
  replace (1 + d + b) with (b + (1 + d)) by omega.
  rewrite power_add; code_simpl.
  rewrite pull_c_i_bot, power_add; simpl; beta_simpl.
  rewrite lower_pull; reflexivity.
Qed.

Lemma bohm_out_wrong_head (h k b : nat) :
  exists s r : ClosedCode, [s, r] [= A /\
  TOP [= r o (K ^ (1 + h) * K ^ k o [BOT] ^ b) o s.
Proof.
  exists (raise^(k+1+h)), (lower^(k+1+h)); bohm_out.
  setoid_rewrite power_add at 1; simpl; code_simpl.
  rewrite lower_k.
  setoid_rewrite power_add; simpl; code_simpl.
  unfold lower at 2; code_simpl.
  rewrite lower_k.
  apply push_top.
Qed.

(* ------------------------------------------------------------------------ *)
(** ** Construction of Bohm tree witnesses *)

Lemma lt_add (p q : nat) : p <= q -> exists r, q = p + r.
Proof.
  intro H; induction H; eauto.
  destruct IHle as [r IH].
  exists (Succ r); rewrite IH; auto.
Qed.

Lemma nle_bot_witness (x : ClosedCode) :
  ~x [= BOT -> exists h k b, K ^ h * K ^ k o [BOT] ^ b [= x.
Proof.
  intro H; apply conv_nle_bot in H.
  rewrite conv_closed in H; destruct H as [y [xy yt]].
  apply weaken_probe in xy; apply weaken_pi in yt.
  dependent induction yt; eauto.
  - admit.
  - admit.
Qed.

(** This follows %\cite{obermeyer2009equational}% pp. 48 Lemma 3.6.11. *)

Theorem A_repairs_pair (i : ClosedCode) :
  ~ i [= BOT -> exists s r, [s, r] [= A /\ I [= r o i o s.
Proof.
  intro H; apply nle_bot_witness in H; destruct H as [h [k [b H]]].
  setoid_rewrite <- H; clear H i.
  destruct h.
  - (* case: correct head variable *)
    simpl; setoid_rewrite beta_i; setoid_rewrite code_eq_b_assoc.
    set (kb := lt_eq_lt_dec k b); destruct kb as [[Hlt | Heq] | Hgt].
    + (* case: too many arguments *)
      apply lt_add in Hlt; destruct Hlt as [d Ed]; subst.
      replace (Datatypes.S k) with (1 + k) by omega.
      setoid_rewrite (@code_le_top _ I) at 1.
      apply bohm_out_too_many_args.
    + (* case: correct number of arguments *)
      subst.
      apply bohm_out_repair.
    + (* case: too few arguments *)
      apply lt_add in Hgt; destruct Hgt as [d Ed]; subst.
      replace (Datatypes.S b + d) with (1 + d + b) by omega.
      setoid_rewrite (@code_le_top _ I) at 1.
      eapply bohm_out_too_few_args.
  - (* case: incorrect head variable *)
    replace (Datatypes.S h) with (1 + h) by omega.
    setoid_rewrite (@code_le_top _ I) at 1.
    apply bohm_out_wrong_head.
Qed.

Corollary A_repairs (i : ClosedCode) : ~ i [= BOT -> I [= A * exp * i.
Proof.
  intro H; apply A_repairs_pair in H; destruct H as [s [r [Ha Hi]]].
  rewrite <- Ha; unfold pair, exp; code_simpl.
  assumption.
Qed.

(* TODO state and prove a [nle_i_witness] lemma
Inductive Increasing : ClosedCode -> Prop :=
  | Increasing_head (h k b : nat) :
      Increasing (K ^ (1 + h) * K ^ k o [BOT] ^ b)
  | Increasing_arg : ???
.

Lemma nle_i_witness (x : ClosedCode) : ~x [= I -> ???.
*)

Theorem A_raises_pair (i : ClosedCode) :
  ~ i [= I -> exists s r, [s, r] [= A /\ TOP [= r o i o s.
Proof.
  admit.
Qed.

Corollary A_raises (i : ClosedCode) : ~ i [= I -> TOP [= A * exp * i.
Proof.
  intro H; apply A_raises_pair in H; destruct H as [s [r [Ha Hi]]].
  rewrite <- Ha; unfold pair, exp; code_simpl.
  assumption.
Qed.

(* TODO the following two theorems need stronger induction hypotheses,
   of higher type *)

Theorem A_repairs' (i : ClosedCode) : ~ i [= BOT -> I [= A * exp * i.
Proof.
  repeat rewrite <- decompile_le.
  do 2 rewrite decompile_app; freeze A in freeze exp in simpl.
  set (i' := decompile i); subst.
  intro H; apply nle_normal_witness in H; destruct H as [n [Hn [ni nb]]].
  rewrite <- ni; clear i i' ni; revert nb.
  induction Hn; intro Hnle.
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

Theorem A_raises' (i : ClosedCode) : ~ i [= I -> TOP [= A * exp * i.
Proof.
  repeat rewrite <- decompile_le.
  do 2 rewrite decompile_app; freeze A in freeze exp in simpl.
  set (i' := decompile i); subst.
  intro H; apply nle_normal_witness in H; destruct H as [n [Hn [ni nb]]].
  rewrite <- ni; clear i i' ni; revert nb.
  induction Hn; intro Hnle.
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
