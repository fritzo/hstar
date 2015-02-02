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

Inductive weak_star
  {Var : Set} (r : relation (Code Var)) : relation (Code Var) :=
  | weak_star_refl {x} : weak_star r x x
  | weak_star_trans {x} y {z} : r x y -> weak_star r y z -> weak_star r x z.
Hint Constructors weak_star.

Lemma weaken_star (Var : Set) (r : relation (Code Var)) (x y : Code Var) :
  star r x y <-> weak_star r x y.
Proof.
  split; intro H; induction H; eauto.
  clear H H0; induction IHstar1; auto.
  apply weak_star_trans with y; auto.
Qed.

Lemma weak_star_flip (Var : Set) (r : relation (Code Var)) (x y : Code Var) :
  weak_star (flip r) x y <-> weak_star r y x.
Proof.
  repeat rewrite <- weaken_star.
  split; intro H; induction H; eauto.
Qed.


Inductive probe {Var : Set} : relation (Code Var) :=
  | probe_refl {x} : probe x x
  | probe_trans {x} y {z} : probe x y -> probe y z -> probe x z
  | probe_top {x} : probe x (x * TOP).
Hint Constructors probe.

Inductive probe_step {Var : Set} : relation (Code Var) :=
  | probe_step_top {x} : probe_step x (x * TOP).
Hint Constructors probe_step.

Lemma weaken_probe (Var : Set) (x y : Code Var) :
  probe x y <-> weak_star probe_step x y.
Proof.
  rewrite <- weaken_star.
  split; intro H; induction H; eauto.
  inversion H; auto.
Qed.


Inductive beta {Var : Set} : relation (Code Var) :=
  | beta_refl {x} : beta x x
  | beta_trans {x} y {z} : beta x y -> beta y z -> beta x z
  | beta_left {x x' y} : beta x x' -> beta (x * y) (x' * y)
  | beta_right {x y y'} : beta y y' -> beta (x * y) (x * y')
  | beta_i {x} : beta (I * x) x
  | beta_k {x y} : beta (K * x * y) x
  | beta_b {x y z} : beta (B * x * y * z) (x * (y * z))
  | beta_c {x y z} : beta (C * x * y * z) (x * z * y)
  | beta_s {x y z} : beta (S * x * y * z) (x * z * (y * z))
  | beta_j_ap {x y z} : beta ((x || y) * z) (x * z || y * z)
  | beta_r_ap {x y z} : beta ((x (+) y) * z) (x * z (+) y * z)
  | beta_r_idem {x} : beta (x (+) x) x
  | beta_r_sym {x y} : beta (x (+) y) (y (+) x)
  | beta_r_sym_sym {w x y z} :
      beta ((w(+)x) (+) (y(+)z)) ((x(+)y) (+) (z(+)w)).
Hint Constructors beta.

Inductive beta_step {Var : Set} : relation (Code Var) :=
  | beta_step_left {x x' y} : beta_step x x' -> beta_step (x * y) (x' * y)
  | beta_step_right {x y y'} : beta_step y y' -> beta_step (x * y) (x * y')
  | beta_step_i {x} : beta_step (I * x) x
  | beta_step_k {x y} : beta_step (K * x * y) x
  | beta_step_b {x y z} : beta_step (B * x * y * z) (x * (y * z))
  | beta_step_c {x y z} : beta_step (C * x * y * z) (x * z * y)
  | beta_step_s {x y z} : beta_step (S * x * y * z) (x * z * (y * z))
  | beta_step_j_ap {x y z} : beta_step ((x || y) * z) (x * z || y * z)
  | beta_step_r_ap {x y z} : beta_step ((x (+) y) * z) (x * z (+) y * z)
  | beta_step_r_idem {x} : beta_step (x (+) x) x
  | beta_step_r_sym {x y} : beta_step (x (+) y) (y (+) x)
  | beta_step_r_sym_sym {w x y z} :
      beta_step ((w(+)x) (+) (y(+)z)) ((x(+)y) (+) (z(+)w)).
Hint Constructors beta_step.

Lemma weaken_beta (Var : Set) (x y : Code Var) :
  beta x y <-> weak_star beta_step x y.
Proof.
  rewrite <- weaken_star.
  split; intro H; induction H; eauto.
  - clear H; induction IHbeta; eauto.
  - clear H; induction IHbeta; eauto.
  - induction H; auto.
Qed.


Inductive test {Var : Set} : relation (Code Var) :=
  | test_refl {x} : test x x
  | test_trans {x} y {z} : test x y -> test y z -> test x z
  | test_left {x x' y} : test x x' -> test (x * y) (x' * y)
  | test_right {x y y'} : test y y' -> test (x * y) (x * y')
  | test_top x : test (TOP * x) TOP
  | test_bot x : test x BOT
  | test_j_left {x y} : test (x || y) x
  | test_j_right {x y} : test (x || y) y.
Hint Constructors test.

Inductive test_step {Var : Set} : relation (Code Var) :=
  | test_step_left {x x' y} : test_step x x' -> test_step (x * y) (x' * y)
  | test_step_right {x y y'} : test_step y y' -> test_step (x * y) (x * y')
  | test_step_top x : test_step (TOP * x) TOP
  | test_step_bot x : test_step x BOT
  | test_step_j_left {x y} : test_step (x || y) x
  | test_step_j_right {x y} : test_step (x || y) y.
Hint Constructors test_step.

Lemma weaken_test (Var : Set) (x y : Code Var) :
  test x y <-> weak_star test_step x y.
Proof.
  rewrite <- weaken_star.
  split; intro H; induction H; eauto.
  - clear H; induction IHtest; eauto.
  - clear H; induction IHtest; eauto.
  - induction H; eauto.
Qed.


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
  autorewrite with beta_safe.
Tactic Notation "beta_simpl" "in" hyp(H) :=
  autorewrite with beta_safe in H.
Tactic Notation "beta_reduce" :=
  autorewrite with beta_safe beta_unsafe.
Tactic Notation "beta_reduce" "in" hyp(H) :=
  autorewrite with beta_safe beta_unsafe in H.
Tactic Notation "code_simpl" :=
  autorewrite with beta_safe code_simpl.
Tactic Notation "code_simpl" "in" hyp(H) :=
  autorewrite with beta_safe code_simpl in H.

(** To avoid nontermination in [beta_reduce],
    we provide a mechanism to "freeze" terms during reduction. *)
Tactic Notation "freeze" reference(c) "in" tactic(tac) :=
  let v := fresh "v" in
  let H := fresh "Hv" in
  assert (exists v, c=v) as H;
  [ exists c; reflexivity
  | destruct H as [v H]; rewrite H; tac; destruct H].


Class Commuting (Var : Set) (r s : relation (Code Var)) :=
  commuting : forall x y z, r x y -> s y z -> exists y', s x y' /\ r y' z.

Tactic Notation
  "commute" ident(x) ident(y) ident(z) constr(xy) constr(yz)
  "as" ident(w) :=
  let xy := fresh x y in
  let yx := fresh y x in
  let yz := fresh y z in
  let zy := fresh z y in
  let xw := fresh x w in
  let wz := fresh w z in
  let H := fresh in
  match type of xy with
    | ?r y x => assert (flip r x y) as xy; [unfold flip; assumption | idtac]
    | ?r x y => idtac
  end;
  match type of yz with
    | ?r z y => assert (flip r y z) as yz; [unfold flip; assumption | idtac]
    | ?r y z => idtac
  end;
  set (H := commuting x y z xy yz);
  destruct H as [w [xw wz]];
  try unfold flip in xw, wz.

Lemma weaken_commuting (Var : Set) (r s r' s' : relation (Code Var)) :
  (forall (x y : Code Var), r x y <-> weak_star r' x y) ->
  (forall (x y : Code Var), s x y <-> weak_star s' x y) ->
  (forall x y z, r' x y -> s' y z -> exists y', s x y' /\ r y' z) ->
  Commuting Var r s.
Proof.
  intros Hr Hs Hweak x y z rxy syz.
  rewrite Hr in rxy.
  rewrite Hs in syz.
  induction rxy; induction syz; eauto.
  - exists x; rewrite Hr, Hs; auto.
  - exists z; rewrite Hr, Hs; split; auto.
    apply weak_star_trans with y; auto.
  - exists x; rewrite Hr, Hs; split; auto.
    apply weak_star_trans with y; auto.
  - admit.
Qed.


Instance probe_reflexive (Var : Set) : Reflexive (@probe Var).
Proof.
  auto.
Qed.

Instance probe_transitive (Var : Set) : Transitive (@probe Var).
Proof.
  intros x y z; apply probe_trans.
Qed.

Instance probe_preorder (Var : Set) : PreOrder (@probe Var).
Proof.
  split; [apply probe_reflexive | apply probe_transitive].
Qed.

Lemma probe_step_probe (Var : Set) (x y : Code Var) :
  probe_step x y -> probe x y.
Proof.
  intro H; inversion H; auto.
Qed.

Ltac simpl_probe_step :=
  repeat
  match goal with
    | [H : probe_step _ _ |- _] => destruct H
  (*
    | [|- probe ?x ?y] => rewrite weaken_probe
    | [H : star probe_step _ _ |- _] => induction H
  *)
    | [H : probe_step ?x ?x -> _ |- _] => clear H
  end;
  eauto.

Instance commuting_flip_probe_probe (Var : Set) :
  Commuting Var (flip probe) probe.
Proof.
  apply (weaken_commuting _ _ _ (flip probe_step) probe_step); auto.
  - intros x y; rewrite weak_star_flip; compute; apply weaken_probe.
  - apply weaken_probe.
  - unfold flip; intros x y z xy yz.
    induction xy; induction yz; eauto.
Qed.


Instance beta_reflexive (Var : Set) : Reflexive (@beta Var).
Proof.
  auto.
Qed.

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

Ltac simpl_beta_step :=
  (* repeat *)
  match goal with
    | [H : beta_step _ _ |- _] => induction H
    | [H : beta_step ?x ?x -> _ |- _] => clear H
  end.

Lemma beta_step_beta (Var : Set) (x y : Code Var) :
  beta_step x y -> beta x y.
Proof.
  intro H; induction H; auto.
Qed.

Instance commuting_flip_beta_beta (Var : Set) : Commuting Var (flip beta) beta.
Proof.
  apply (weaken_commuting _ _ _ (flip beta_step) beta_step); auto.
  - intros x y; rewrite weak_star_flip; compute; apply weaken_beta.
  - apply weaken_beta.
  - compute; intros x y z xy yz.
    induction xy; induction yz; auto.
Admitted. 

Instance commuting_flip_beta_probe (Var : Set) :
  Commuting Var (flip beta) probe.
Proof.
  apply (weaken_commuting _ _ _ (flip beta_step) probe_step); auto.
  - intros x y; rewrite weak_star_flip; compute; apply weaken_beta.
  - apply weaken_probe.
  - compute; intros x y z xy yz.
    destruct yz.
    exists (x * TOP); repeat split; auto.
    apply (@weak_star_trans _ _ x0 x x) in xy; auto.
    rewrite <- weaken_beta in xy; auto.
Qed.

Instance commuting_beta_probe (Var : Set) : Commuting Var beta probe.
Proof.
  apply (weaken_commuting _ _ _ beta_step probe_step); auto.
  - apply weaken_beta.
  - apply weaken_probe.
  - compute; intros x y z xy yz.
    induction xy; destruct yz; eauto.
Admitted.


Instance test_transitive (Var : Set) : Transitive (@test Var).
Proof.
  intros x y z Hxy Hyz; apply test_trans with y; auto.
Qed.

Instance test_reflexive (Var : Set) : Reflexive (@test Var).
Proof.
  auto.
Qed.

Instance test_preorder (Var : Set) : PreOrder (@test Var).
Proof.
  split; [apply test_reflexive | apply test_transitive].
Qed.

Instance code_ap_test (Var : Set) : Proper (test ++> test ++> test) (@code_ap Var).
Proof.
  intros x x' Hx y y' Hy; transitivity (x * y'); auto.
Qed.

Lemma beta_step_test_top (Var : Set) (x y : Code Var) :
  beta_step x y -> (test x TOP <-> test y TOP).
Proof.
  intro Hb; split; induction Hb;
  intro Ht; rewrite weaken_test in Ht; induction Ht; auto.
Admitted.

Lemma beta_test_top (Var : Set) (x y : Code Var) :
  beta x y -> (test x TOP <-> test y TOP).
Proof.
  intro Hb; rewrite weaken_beta in Hb; induction Hb; try tauto.
  transitivity (test y TOP); auto.
  apply beta_step_test_top; auto.
Qed.

Lemma probe_test_top (Var : Set) (x y : Code Var) :
  probe x y -> test x TOP -> test y TOP.
Proof.
  intro Hp; rewrite weaken_probe in Hp; induction Hp; simpl_probe_step.
Qed.


Instance conv_proper_test_step (Var : Set) :
  Proper (test_step --> impl) (@conv Var).
Proof.
  intros x x' xx' [y [z [xy [yz zt]]]]; compute in xx';
  induction xx'; unfold conv; eauto.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
Qed.

Instance conv_proper_test (Var : Set) : Proper (test --> impl) (@conv Var).
Proof.
  intros x x' xx' Hc.
  compute in xx'; apply weaken_test in xx'.
  induction xx'; auto.
  rewrite H; auto.
Qed.

Instance conv_proper_beta (Var : Set) :
  Proper (beta ==> iff) (@conv Var).
Proof.
  intros x x' xx'; split.
  - intros [y [z [xy [yz zt]]]].
    commute x' x y xx' xy as y'; exists y'.
    commute y' y z y'y yz as z'; exists z'.
    repeat split; auto.
    rewrite <- (beta_test_top _ _ _ z'z); auto.
  - intros [y' [z' [x'y' [y'z' z't]]]].
    commute x x' y' xx' x'y' as y; exists y.
    exists z'; repeat split; auto.
    transitivity y'; auto.
Qed.

Instance conv_proper_probe (Var : Set) : Proper (probe ==> iff) (@conv Var).
Proof.
  intros x x' xx'; split.
  - intros [y [z [xy [yz zt]]]].
    commute x' x y xx' xy as y'; exists y'.
    commute z y y' yz y'y as z'; exists z'.
    repeat split; auto.
    apply probe_test_top with z; auto.
  - intros [y' [z' [x'y' [y'z' z't]]]].
    exists y', z'; repeat split; auto.
    transitivity x'; auto.
Qed.

Lemma conv_top (Var : Set) : conv (TOP : Code Var).
Proof.
  exists TOP, TOP; repeat split; auto.
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

Lemma heads_test_bot (Var : Set) (x y : Code Var) :
  test x y -> heads BOT x -> heads BOT y.
Proof.
  intros Ht; induction Ht; intros; heads.
Qed.

Lemma not_conv_heads_bot (Var : Set) (x : Code Var) : heads BOT x -> ~ conv x.
Proof.
  intros H [y [z [xy [yz zt]]]].
  apply (heads_probe _ _ _ y) in H; auto.
  apply (heads_beta_bot _ _ z) in H; auto.
  apply (heads_test_bot _ _ TOP) in H; auto.
  inversion H; auto.
Qed.

Lemma not_conv_bot (Var : Set) : ~ conv (BOT : Code Var).
Proof.
  apply not_conv_heads_bot; heads.
Qed.
Hint Resolve not_conv_bot.
