(** * Combinatory algebra with parametric variables *)

Definition Succ := S%nat.  (* an alias for later *)

Require Import Coq.Program.Basics.
Require Import Coq.Setoids.Setoid.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Export Notations.

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

Inductive probe {Var : Set} : Code Var -> Code Var -> Prop :=
  | probe_refl {x} : probe x x
  | probe_trans {x} y {z} : probe x y -> probe y z -> probe x z
  | probe_top {x y} : probe x y -> probe x (y * TOP).

Inductive beta {Var : Set} : Code Var -> Code Var -> Prop :=
  | beta_refl {x} : beta x x
  | beta_trans {x} y {z} : beta x y -> beta y z -> beta x z
  | beta_ap_left {x x' y} : beta x x' -> beta (x * y) (x' * y)
  | beta_ap_right {x y y'} : beta y y' -> beta (x * y) (x * y')
  | beta_i {x} : beta (I * x) x
  | beta_k {x y} : beta (K * x * y) x
  | beta_b {x y z} : beta (B * x * y * z) (x * (y * z))
  | beta_c {x y z} : beta (C * x * y * z) (x * z * y)
  | beta_s {x y z} : beta (S * x * y * z) (x * z * (y * z))
  | beta_j_ap {x y z} : beta ((x || y) * z) (x * z || y * z)
  | beta_r_ap {x y z} : beta ((x (+) y) * z) (x * z (+) y * z)
  | beta_r_idem {x} : beta (x (+) x) x
  | beta_r_sym {x y} : beta (x (+) y) (y (+) x)
  | beta_r_sym_sym {w x y z} : beta ((w(+)x) (+) (y(+)z)) ((x(+)y) (+) (z(+)w)).

Inductive test {Var : Set} : Code Var -> Code Var -> Prop :=
  | test_refl {x} : test x x
  | test_trans {x} y {z} : test x y -> test y z -> test x z
  | test_ap_left {x x' y} : test x x' -> test (x * y) (x' * y)
  | test_ap_right {x y y'} : test y y' -> test (x * y) (x * y')
  | test_top x : test (TOP * x) TOP
  | test_bot x : test x BOT
  | test_j_left {x y} : test (x || y) x
  | test_j_right {x y} : test (x || y) y.

Definition conv {Var : Set} (x : Code Var) : Prop :=
  exists y z, probe x y /\ beta y z /\ test z TOP.

Inductive prob {Var : Set} : Code Var -> Prop :=
  | prob_top : prob TOP
  | prob_bot : prob BOT
  | prob_r p q : prob p -> prob q -> prob (p (+) q).

Definition pconv {Var : Set} (x p : Code Var) : Prop :=
  prob p /\ exists y z, probe x y /\ beta y z /\ test z p.

Hint Constructors probe.
Hint Constructors beta.
Hint Constructors test.
Hint Constructors prob.

Definition Beta_i (Var : Set) := (@beta_i Var).
Definition Beta_k (Var : Set) := (@beta_k Var).
Definition Beta_b (Var : Set) := (@beta_b Var).
Definition Beta_c (Var : Set) := (@beta_c Var).
Definition Beta_s (Var : Set) := (@beta_s Var).
Definition Beta_j_ap (Var : Set) := (@beta_j_ap Var).
Definition Beta_r_ap (Var : Set) := (@beta_r_ap Var).
Definition Beta_r_idem (Var : Set) := (@beta_r_idem Var).

Hint Rewrite Beta_i Beta_k Beta_b Beta_c Beta_j_ap Beta_r_ap Beta_r_idem
  : beta_safe.
Hint Rewrite Beta_s : beta_unsafe.

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
  intros x y z; apply probe_trans.
Qed.

Instance probe_preorder (Var : Set) : PreOrder (@probe Var).
Proof.
  split; [apply probe_reflexive | apply probe_transitive].
Qed.

Instance probe_confluent (Var : Set) :
  Commuting (flip (@probe Var)) (@probe Var).
Proof.
  unfold flip; intros x y z xy yz; induction xy; induction yz; eauto.
Admitted.


Instance beta_reflexive (Var : Set) : Reflexive (@beta Var).
Proof. auto. Qed.

Instance beta_transitive (Var : Set) : Transitive (@beta Var).
Proof.
  intros x y z; apply beta_trans.
Qed.

Instance beta_preorder (Var : Set) : PreOrder (@beta Var).
Proof.
  split; [apply beta_reflexive | apply beta_transitive].
Qed.

Instance code_ap_beta (Var : Set) :
  Proper (beta ==> beta ==> beta) (@code_ap Var).
Proof.
  intros x x' Hx y y' Hy; transitivity (x * y'); auto.
Qed.

Instance beta_confluent (Var : Set) :
  Commuting (flip (@beta Var)) (@beta Var).
Proof.
  unfold flip; intros x y z xy yz; induction xy; induction yz; auto.
Admitted.


Instance test_transitive (Var : Set) : Transitive (@test Var).
Proof.
  intros x y z Hxy Hyz; apply test_trans with y; auto.
Qed.

Instance test_reflexive (Var : Set) : Reflexive (@test Var).
Proof. auto. Qed.

Instance test_preorder (Var : Set) : PreOrder (@test Var).
Proof.
  split; [apply test_reflexive | apply test_transitive].
Qed.

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
