(** * Convergence *)

Require Import Coq.Program.Basics.
Require Import Coq.Setoids.Setoid.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Export Substitution.

Definition conv {Var : Set} (x : Code Var) : Prop :=
  exists y, probe (close x) y /\ pi y TOP.

Lemma conv_close (Var : Set) (x : Code Var) : conv (close x) <-> conv x.
Proof.
  unfold conv; code_simpl; tauto.
Qed.

Inductive prob {Var : Set} : Code Var -> Prop :=
  | prob_top : prob TOP
  | prob_bot : prob BOT
  | prob_r p q : prob p -> prob q -> prob (p (+) q).
Hint Constructors prob.

Definition pconv {Var : Set} (x : Code Var) (p : Code Empty_set) : Prop :=
  prob p /\ exists y, probe (x @ sub_top) y /\ pi y p.

Ltac wlog_closed x :=
  let cx := fresh "c" x in
  let Ex := fresh "E" x in
  let Hcx := fresh "H" cx in
  rename x into cx;
  assert (exists x, x = close cx) as Ex; [exists (close cx); reflexivity|];
  destruct Ex as [x Ex];
  assert (close x = x) as Hcx; [rewrite -> Ex; apply close_idempotent|];
  repeat
  match goal with
    | [ H : conv x |- _] =>
        rewrite <- conv_close in H;
        replace (close cx) with x in H
    | [|- conv x ] =>
        rewrite <- conv_close;
        replace (close cx) with x
    | _ => idtac
  end.

Instance conv_proper_beta (Var : Set) :
  Proper (beta ==> iff) (@conv Var).
Proof.
  intros x x' xx'; split; intro H;
  wlog_closed x; wlog_closed x';
  apply beta_close in xx'; rewrite <- Ex in xx'; rewrite <- Ex' in xx'.
  - destruct H as [y [xy yt]].
    rewrite <- Ex in xy.
    commute x' x y xx' xy as y'; exists y'.
    split; [rewrite <- Ex'; auto|].
    rewrite <- (beta_pi_top _ _ _ y'y); auto.
  - destruct H as [y' [x'y' y't]].
    rewrite <- Ex' in x'y'.
    commute x x' y' xx' x'y' as y; exists y.
    split; [rewrite <- Ex; auto|].
    transitivity y'; auto.
    rewrite yy'; auto.
Qed.

Instance conv_proper_pi (Var : Set) : Proper (pi --> impl) (@conv Var).
Proof.
  intros x x' xx' [y [xy yt]];
  wlog_closed x; wlog_closed x';
  apply pi_close in xx'; rewrite <- Ex in xx'; rewrite <- Ex' in xx'.
  rewrite <- Ex in xy.
  commute x' x y xx' xy as y'; exists y'.
  split; [rewrite <- Ex'; auto| eauto].
Qed.

Instance conv_proper_probe (Var : Set) : Proper (probe ==> iff) (@conv Var).
Proof.
  intros x x' xx'; split; intro H;
  wlog_closed x; wlog_closed x';
  apply probe_close in xx'; rewrite <- Ex in xx'; rewrite <- Ex' in xx'.
  - destruct H as [y [xy yt]].
    rewrite <- Ex in xy.
    commute x' x y xx' xy as y'; exists y'.
    split; [rewrite <- Ex'; auto|].
    apply probe_pi_top with y; auto.
  - destruct H as [y' [x'y' y't]].
    exists y'; split; auto.
    rewrite <- Ex' in x'y'.
    transitivity x'; auto.
    rewrite <- Ex; auto.
Qed.

Lemma conv_top (Var : Set) : conv (TOP : Code Var).
Proof.
  exists TOP; split; auto.
Qed.
Hint Resolve conv_top.

(** ** A [heads] relation for proving nontermination *)

Inductive heads {Var : Set} : relation (Code Var) :=
  | heads_refl x : heads x x
  | heads_ap h x y : heads h x -> heads h (x * y).

Ltac heads :=
  auto using heads_refl, heads_ap;
  match goal with
  | [H : heads ?x ?y |- _] => inversion_clear H; heads
  end.

Lemma heads_close (Var : Set) (h x : Code Var) :
  heads h x -> heads (close h) (close x).
Proof.
  intro H; induction H; simpl; compute; heads.
Qed.

Lemma heads_probe (Var : Set) (h x y : Code Var) :
  probe x y -> heads h x -> heads h y.
Proof.
  rewrite weaken_probe.
  intro xy; induction xy; simpl_probe_step; heads.
Qed.

Lemma heads_beta_bot (Var : Set) (x y : Code Var) :
  beta x y -> heads BOT x -> heads BOT y.
Proof.
  intros Ht; induction Ht; intros; heads.
Qed.

Lemma heads_pi_bot (Var : Set) (x y : Code Var) :
  pi x y -> heads BOT x -> heads BOT y.
Proof.
  intros Ht; induction Ht; intros; heads.
Qed.

Lemma not_conv_heads_bot (Var : Set) (x : Code Var) : heads BOT x -> ~ conv x.
Proof.
  intros H [y [xy yt]].
  apply (heads_close) in H.
  apply (heads_probe _ _ _ y) in H; auto.
  apply (heads_pi_bot _ _ TOP) in H; auto.
  inversion H; auto.
Qed.

Lemma not_conv_bot (Var : Set) : ~ conv (BOT : Code Var).
Proof.
  apply not_conv_heads_bot; heads.
Qed.
Hint Resolve not_conv_bot.
