(** * Convergence *)

Require Import Coq.Program.Basics.
Require Import Coq.Setoids.Setoid.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Export Substitution.

Definition conv {Var : Set} (x : Code Var) : Prop :=
  exists y, probe x y /\ pi y TOP.

Inductive prob {Var : Set} : Code Var -> Prop :=
  | prob_top : prob TOP
  | prob_bot : prob BOT
  | prob_r p q : prob p -> prob q -> prob (p (+) q).
Hint Constructors prob.

Definition pconv {Var : Set} (x p : Code Var) : Prop :=
  prob p /\ exists y, probe x y /\ pi y p.

Instance conv_proper_beta (Var : Set) :
  Proper (beta ==> iff) (@conv Var).
Proof.
  intros x x' xx'; split.
  - intros [y [xy yt]].
    commute x' x y xx' xy as y'; exists y'.
    split; auto.
    rewrite <- (beta_pi_top _ _ _ y'y); auto.
  - intros [y' [x'y' y't]].
    commute x x' y' xx' x'y' as y; exists y.
    split; auto.
    transitivity y'; auto.
    rewrite yy'; auto.
Qed.

Instance conv_proper_pi (Var : Set) : Proper (pi --> impl) (@conv Var).
Proof.
  intros x x' xx' [y [xy yt]]; compute in xx'.
    commute x' x y xx' xy as y'; exists y'.
    split; auto.
    transitivity y; auto.
Qed.

Instance conv_proper_probe (Var : Set) : Proper (probe ==> iff) (@conv Var).
Proof.
  intros x x' xx'; split.
  - intros [y [xy yt]].
    commute x' x y xx' xy as y'; exists y'.
    repeat split; auto.
    apply probe_pi_top with y; auto.
  - intros [y' [x'y' y't]].
    exists y'; split; auto.
    transitivity x'; auto.
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
  apply (heads_probe _ _ _ y) in H; auto.
  apply (heads_pi_bot _ _ TOP) in H; auto.
  inversion H; auto.
Qed.

Lemma not_conv_bot (Var : Set) : ~ conv (BOT : Code Var).
Proof.
  apply not_conv_heads_bot; heads.
Qed.
Hint Resolve not_conv_bot.
