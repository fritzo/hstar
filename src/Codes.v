(** * Combinatory algebra with parametric variables *)

Definition Succ := S%nat.  (* an alias for later *)

Require Import Coq.Program.Basics.
Require Import Coq.Program.Equality.
Require Import Coq.Setoids.Setoid.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Export Notations.

(** ** Codes *)

Inductive code {Var : Set} : Set :=
  | code_var : Var -> code
  | code_ap : code -> code -> code
  | code_top : code
  | code_bot : code
  | code_j : code
  | code_r : code
  | code_i : code
  | code_k : code
  | code_b : code
  | code_c : code
  | code_s : code.
Hint Constructors code.
Definition Code (Var : Set) := @code Var.

Notation "'TOP'" := code_top : code_scope.
Notation "'BOT'" := code_bot : code_scope.
Notation "'J'" := code_j : code_scope.
Notation "'R'" := code_r : code_scope.
Notation "'I'" := code_i : code_scope.
Notation "'K'" := code_k : code_scope.
Notation "'B'" := code_b : code_scope.
Notation "'C'" := code_c : code_scope.
Notation "'S'" := code_s : code_scope.

Open Scope code_scope.
Delimit Scope code_scope with code.
Bind Scope code_scope with code.

Notation "x * y" := (code_ap x y) : code_scope.
Notation "x 'o' y" := (code_b * x * y) : code_scope.
Notation "x || y" := (code_j * x * y) : code_scope.
Notation "x (+) y" := (code_r * x * y) : code_scope.

Definition code_join {Var : Set} x y : Code Var := x || y.

(** ** Reduction relations *)

Inductive star {Var : Set} (r : relation (Code Var)) : relation (Code Var) :=
  | star_step {x y} : r x y -> star r x y
  | star_refl {x} : star r x x
  | star_trans {x} y {z} : star r x y -> star r y z -> star r x z.
Hint Constructors star.

Inductive weak_star {Var : Set} (r : relation (Code Var)) :
  relation (Code Var) :=
  | weak_star_step {x y} : r x y -> weak_star r x y
  | weak_star_refl {x} : weak_star r x x
  | weak_star_trans {x} y {z} : r x y -> weak_star r y z -> weak_star r x z.
Hint Constructors weak_star.

Inductive astar {Var : Set} (r : relation (Code Var)) : relation (Code Var) :=
  | astar_step {x y} : r x y -> astar r x y
  | astar_refl {x} : astar r x x
  | astar_trans {x} y {z} : astar r x y -> astar r y z -> astar r x z
  | astar_left {x x' y} : astar r x x' -> astar r (x * y) (x' * y)
  | astar_right {x y y'} : astar r y y' -> astar r (x * y) (x * y').
Hint Constructors astar.

Inductive weak_astar {Var : Set} (r : relation (Code Var)) :
  relation (Code Var) :=
  | weak_astar_step {x y} : r x y -> weak_astar r x y
  | weak_astar_left {x x' y} :
      weak_astar r x x' -> weak_astar r (x * y) (x' * y)
  | weak_astar_right {x y y'} :
      weak_astar r y y' -> weak_astar r (x * y) (x * y').
Hint Constructors weak_astar.

Lemma weaken_star (Var : Set) (r : relation (Code Var)) (x y : Code Var) :
  star r x y <-> weak_star r x y.
Proof.
  split; intro H; induction H; eauto.
  clear H H0; induction IHstar1; eauto.
Qed.

Lemma weaken_astar (Var : Set) (r : relation (Code Var)) (x y : Code Var) :
  astar r x y <-> weak_star (weak_astar r) x y.
Proof.
  rewrite <- weaken_star.
  split; intro H; induction H; eauto.
  - clear H; induction IHastar; eauto.
  - clear H; induction IHastar; eauto.
  - induction H; eauto.
Qed.

Inductive probe_step {Var : Set} : Code Var -> Code Var -> Prop :=
  | probe_top {x} : probe_step x (x * TOP).
Hint Constructors probe_step.

Definition probe {Var : Set} : relation (Code Var) := star probe_step.
Hint Unfold probe.

Inductive beta_step {Var : Set} : Code Var -> Code Var -> Prop :=
  | beta_i {x} : beta_step (I * x) x
  | beta_k {x y} : beta_step (K * x * y) x
  | beta_b {x y z} : beta_step (B * x * y * z) (x * (y * z))
  | beta_c {x y z} : beta_step (C * x * y * z) (x * z * y)
  | beta_s {x y z} : beta_step (S * x * y * z) (x * z * (y * z))
  | beta_j_ap {x y z} : beta_step ((x || y) * z) (x * z || y * z)
  | beta_r_ap {x y z} : beta_step ((x (+) y) * z) (x * z (+) y * z)
  | beta_r_idem {x} : beta_step (x (+) x) x
  | beta_r_sym {x y} : beta_step (x (+) y) (y (+) x)
  | beta_r_sym_sym {w x y z} :
      beta_step ((w(+)x) (+) (y(+)z)) ((x(+)y) (+) (z(+)w)).
Hint Constructors beta_step.

Definition beta {Var : Set} : relation (Code Var) := astar beta_step.
Hint Unfold beta.

Inductive test_step {Var : Set} : Code Var -> Code Var -> Prop :=
  | test_top x : test_step (TOP * x) TOP
  | test_bot x : test_step x BOT
  | test_j_left {x y} : test_step (x || y) x
  | test_j_right {x y} : test_step (x || y) y.
Hint Constructors test_step.

Definition test {Var : Set} : relation (Code Var) := astar test_step.
Hint Unfold test.

Definition conv {Var : Set} (x : Code Var) : Prop :=
  exists y z, probe x y /\ beta y z /\ test z TOP.

Inductive prob {Var : Set} : Code Var -> Prop :=
  | prob_top : prob TOP
  | prob_bot : prob BOT
  | prob_r p q : prob p -> prob q -> prob (p (+) q).
Hint Constructors prob.

Definition pconv {Var : Set} (x p : Code Var) : Prop :=
  prob p /\ exists y z, probe x y /\ beta y z /\ test z p.

Hint Rewrite @beta_i @beta_k @beta_b @beta_c @beta_j_ap @beta_r_ap @beta_r_idem
  : beta_safe.
Hint Rewrite @beta_s : beta_unsafe.

Tactic Notation "beta_simpl" :=
  timeout 10
  autorewrite with beta_safe.
Tactic Notation "beta_simpl" "in" hyp(H) :=
  timeout 10
  autorewrite with beta_safe in H.
Tactic Notation "beta_reduce" :=
  timeout 10
  autorewrite with beta_safe beta_unsafe.
Tactic Notation "beta_reduce" "in" hyp(H) :=
  timeout 10
  autorewrite with beta_safe beta_unsafe in H.
Tactic Notation "code_simpl" :=
  timeout 10
  autorewrite with beta_safe code_simpl.
Tactic Notation "code_simpl" "in" hyp(H) :=
  timeout 10
  autorewrite with beta_safe code_simpl in H.

(** To avoid nontermination in [beta_reduce],
    we provide a mechanism to "freeze" terms during reduction. *)
Tactic Notation "freeze" reference(c) "in" tactic(tac) :=
  let v := fresh "v" in
  let H := fresh "Hv" in
  assert (exists v, c=v) as H;
  [ exists c; reflexivity
  | destruct H as [v H]; rewrite H; tac; destruct H].


Class Commuting {a} (r s : relation a) :=
  commuting : forall x y z, r x y -> s y z -> exists y', s x y' /\ r y' z.

Ltac commute x y z xy yz :=
  let w := fresh "w" in
  let xw := fresh x w in
  let wz := fresh w z in
  let H := fresh in
  set (H := commuting _ _ x y z xy yz);
  destruct H as [w [xw wz]].


Instance probe_reflexive (Var : Set) : Reflexive (@probe Var).
Proof. auto. Qed.

Instance probe_transitive (Var : Set) : Transitive (@probe Var).
Proof.
  intros x y z; apply star_trans.
Qed.

Instance probe_preorder (Var : Set) : PreOrder (@probe Var).
Proof.
  split; [apply probe_reflexive | apply probe_transitive].
Qed.

Instance probe_subrelation (Var : Set) :
  @subrelation (Code Var) probe_step probe.
Proof. simpl_relation. Qed.

Ltac simpl_probe_step :=
  repeat
  match goal with
    | [H : probe_step _ _ |- _] => destruct H
    | [H : probe_step ?x ?x -> _ |- _] => clear H
  end.

Instance probe_confluent (Var : Set) :
  Commuting (flip (@probe Var)) (@probe Var).
Proof.
  unfold flip, probe; intros x y z xy yz.
  rewrite weaken_star in xy, yz.
  induction xy; induction yz; eauto; simpl_probe_step.
  - exists (x * TOP); auto.
  - exists z; split; auto.
    apply weaken_star; auto.
  - exists z; split; auto.
    apply weaken_star.
    apply weak_star_trans with (x * TOP); auto.
  - apply IHxy; auto.
  - exists z0; split; auto.
    apply weaken_star.
    apply weak_star_trans with (x * TOP); auto.
  - apply IHxy; auto.
Qed.


Instance beta_reflexive (Var : Set) : Reflexive (@beta Var).
Proof. auto. Qed.

Instance beta_transitive (Var : Set) : Transitive (@beta Var).
Proof.
  intros x y z; apply astar_trans.
Qed.

Instance beta_preorder (Var : Set) : PreOrder (@beta Var).
Proof.
  split; [apply beta_reflexive | apply beta_transitive].
Qed.

Instance beta_subrelation (Var : Set) :
  @subrelation (Code Var) beta_step beta.
Proof. simpl_relation. Qed.

Instance code_ap_beta (Var : Set) :
  Proper (beta ==> beta ==> beta) (@code_ap Var).
Proof.
  intros x x' Hx y y' Hy; transitivity (x * y'); auto.
Qed.

Ltac beta_confluent_induction :=
  timeout 10
  repeat
  match goal with
    | [H : weak_star _ _ _ |- _] => induction H
    | [H : weak_astar _ _ _ |- _] => induction H
  end.

Instance beta_confluent (Var : Set) :
  Commuting (flip (@beta Var)) (@beta Var).
Proof.
  unfold flip, beta; intros x y z xy yz.
  rewrite weaken_astar in xy, yz.
  induction xy; induction yz; eauto.
Admitted.


Instance test_transitive (Var : Set) : Transitive (@test Var).
Proof.
  intros x y z Hxy Hyz; apply astar_trans with y; auto.
Qed.

Instance test_reflexive (Var : Set) : Reflexive (@test Var).
Proof. auto. Qed.

Instance test_preorder (Var : Set) : PreOrder (@test Var).
Proof.
  split; [apply test_reflexive | apply test_transitive].
Qed.

Instance test_subrelation (Var : Set) :
  @subrelation (Code Var) test_step test.
Proof. simpl_relation. Qed.

Instance code_ap_test (Var : Set) : Proper (test ++> test ++> test) (@code_ap Var).
Proof.
  intros x x' Hx y y' Hy; transitivity (x * y'); auto.
Qed.

Instance test_beta_to_beta_test (Var : Set) :
  Commuting (@test Var) (@beta Var).
Proof.
  intros x y z xy yz; induction xy; induction yz; auto.
Admitted.

Instance beta_test_confluent (Var : Set) :
  Commuting (flip (@beta Var)) (@test Var).
Proof.
Admitted.


Lemma conv_top (Var : Set) : conv (TOP : Code Var).
Proof.
  exists TOP, TOP; repeat split; auto.
Qed.
Hint Resolve conv_top.

Lemma conv_join_left (Var : Set) (w x : Code Var) : conv w -> conv (w || x).
Proof.
  intros [y [z [wy [yz zt]]]].
Admitted.
Hint Resolve conv_join_left.

Lemma conv_join_right (Var : Set) (w x : Code Var) : conv x -> conv (w || x).
Proof.
  intros [y [z [xy [yz zt]]]].
Admitted.
Hint Resolve conv_join_right.

Lemma not_conv_bot (Var : Set) : ~ conv (BOT : Code Var).
Proof.
Admitted.
Hint Resolve not_conv_bot.


Instance conv_proper_probe (Var : Set) : Proper (probe ==> iff) (@conv Var).
Proof.
Admitted.

Instance conv_proper_beta (Var : Set) : Proper (beta ==> iff) (@conv Var).
Proof.
  intros x x' xx'; split; intros [y [z [xy [yz zt]]]].
  (* OLD
    beta_confluent x x' y xx' xy.
    intros Hc; induction Hc; apply conv_approx; admit.
  intros Hc; induction Hc; apply conv_approx; rewrite xx'; auto.
  *)
Admitted.

Instance conv_proper_test (Var : Set) : Proper (test --> impl) (@conv Var).
Proof.
  compute; intros x x' xx' Ha.
Admitted.
