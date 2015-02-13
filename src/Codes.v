(** * Combinatory algebra with parametric variables *)

Definition Succ := S%nat.  (* an alias for later *)

Require Import Coq.Program.Basics.
Require Import Coq.Program.Equality.
Require Import Coq.Setoids.Setoid.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Export Notations.

(** ** Codes *)

Inductive Code {Var : Set} : Set :=
  | code_var : Var -> Code
  | code_ap : Code -> Code -> Code
  | code_top : Code
  | code_bot : Code
  | code_j : Code
  | code_r : Code
  | code_i : Code
  | code_k : Code
  | code_b : Code
  | code_c : Code
  | code_s : Code.
Arguments Code : default implicits.
Hint Constructors Code.
Definition Closed := Code Empty_set.

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
Bind Scope code_scope with Code.

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


Inductive pi {Var : Set} : relation (Code Var) :=
  | pi_refl {x} : pi x x
  | pi_trans {x} y {z} : pi x y -> pi y z -> pi x z
  | pi_left {x x' y} : pi x x' -> pi (x * y) (x' * y)
  | pi_right {x y y'} : pi y y' -> pi (x * y) (x * y')
  | pi_i {x} : pi (I * x) x
  | pi_k {x y} : pi (K * x * y) x
  | pi_b {x y z} : pi (B * x * y * z) (x * (y * z))
  | pi_c {x y z} : pi (C * x * y * z) (x * z * y)
  | pi_s {x y z} : pi (S * x * y * z) (x * z * (y * z))
  | pi_j_ap {x y z} : pi ((x || y) * z) (x * z || y * z)
  | pi_r_ap {x y z} : pi ((x (+) y) * z) (x * z (+) y * z)
  | pi_r_idem {x} : pi (x (+) x) x
  | pi_r_sym {x y} : pi (x (+) y) (y (+) x)
  | pi_r_sym_sym {w x y z} :
      pi ((w(+)x) (+) (y(+)z)) ((x(+)y) (+) (z(+)w))
  | pi_top x : pi TOP x
  | pi_bot x : pi x BOT
  | pi_j_left {x y} : pi (x || y) x
  | pi_j_right {x y} : pi (x || y) y.
Hint Constructors pi.

Inductive pi_step {Var : Set} : relation (Code Var) :=
  | pi_step_left {x x' y} : pi_step x x' -> pi_step (x * y) (x' * y)
  | pi_step_right {x y y'} : pi_step y y' -> pi_step (x * y) (x * y')
  | pi_step_i {x} : pi_step (I * x) x
  | pi_step_k {x y} : pi_step (K * x * y) x
  | pi_step_b {x y z} : pi_step (B * x * y * z) (x * (y * z))
  | pi_step_c {x y z} : pi_step (C * x * y * z) (x * z * y)
  | pi_step_s {x y z} : pi_step (S * x * y * z) (x * z * (y * z))
  | pi_step_j_ap {x y z} : pi_step ((x || y) * z) (x * z || y * z)
  | pi_step_r_ap {x y z} : pi_step ((x (+) y) * z) (x * z (+) y * z)
  | pi_step_r_idem {x} : pi_step (x (+) x) x
  | pi_step_r_sym {x y} : pi_step (x (+) y) (y (+) x)
  | pi_step_r_sym_sym {w x y z} :
      pi_step ((w(+)x) (+) (y(+)z)) ((x(+)y) (+) (z(+)w))
  | pi_step_top x : pi_step TOP x
  | pi_step_bot x : pi_step x BOT
  | pi_step_j_left {x y} : pi_step (x || y) x
  | pi_step_j_right {x y} : pi_step (x || y) y.
Hint Constructors pi_step.

Lemma weaken_pi (Var : Set) (x y : Code Var) :
  pi x y <-> weak_star pi_step x y.
Proof.
  rewrite <- weaken_star.
  split; intro H; induction H; eauto.
  - clear H; induction IHpi; eauto.
  - clear H; induction IHpi; eauto.
  - induction H; auto.
Qed.


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
  - admit. (* TODO also assume r == star r and s == star s,
              then use strong induction *)
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

Instance beta_step_subrelation (Var : Set) :
  (@subrelation (Code Var)) beta_step beta.
Proof.
  intros x y H; induction H; eauto.
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
    (* TODO try induction over just one variable,
       mapping beta to beta.
       The only problem is with steps that are the same (use refl)
       and in beta_r_ when redexes intersect.
       Try to write a tactic matching against beta constructors. *)
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
  - compute; intros x y z xy yz; destruct yz; exists (x * TOP); split; auto.
    rewrite xy; reflexivity.
Qed.


Instance pi_reflexive (Var : Set) : Reflexive (@pi Var).
Proof.
  auto.
Qed.

Instance pi_transitive (Var : Set) : Transitive (@pi Var).
Proof.
  intros x y z; apply pi_trans.
Qed.

Instance pi_preorder (Var : Set) : PreOrder (@pi Var).
Proof.
  split; [apply pi_reflexive | apply pi_transitive].
Qed.

Instance pi_step_pi_subrelation (Var : Set) :
  (@subrelation (Code Var)) pi_step pi.
Proof.
  intros x y H; induction H; eauto.
Qed.

Instance beta_step_pi_subrelation (Var : Set) :
  (@subrelation (Code Var)) beta_step pi.
Proof.
  intros x y H; induction H; eauto.
Qed.

Instance beta_pi_subrelation (Var : Set) : (@subrelation (Code Var)) beta pi.
Proof.
  intros x y Hb; induction Hb; eauto.
Qed.

Instance pi_proper_beta (Var : Set) : Proper (beta --> beta ++> impl) (@pi Var).
Proof.
  intros x x' xx' y y' yy' Hp; compute in yy'.
  apply beta_pi_subrelation in xx'; rewrite xx'.
  apply beta_pi_subrelation in yy'; rewrite <- yy'.
  auto.
Qed.

Instance code_ap_pi (Var : Set) :
  Proper (pi ==> pi ==> pi) (@code_ap Var).
Proof.
  intros x x' Hx y y' Hy; transitivity (x * y'); auto.
Qed.

Ltac simpl_pi_step :=
  (* repeat *)
  match goal with
    | [H : pi_step _ _ |- _] => induction H
    | [H : pi_step ?x ?x -> _ |- _] => clear H
  end.

Lemma pi_step_pi (Var : Set) (x y : Code Var) :
  pi_step x y -> pi x y.
Proof.
  intro H; induction H; auto.
Qed.

Instance commuting_flip_pi_pi (Var : Set) : Commuting Var (flip pi) pi.
Proof.
  apply (weaken_commuting _ _ _ (flip pi_step) pi_step); auto.
  - intros x y; rewrite weak_star_flip; compute; apply weaken_pi.
  - apply weaken_pi.
  - compute; intros x y z xy yz.
    induction xy; induction yz; auto.
    (* TODO similar to commuting_flip_beta_beta *)
Admitted. 

Instance commuting_flip_pi_probe (Var : Set) :
  Commuting Var (flip pi) probe.
Proof.
  apply (weaken_commuting _ _ _ (flip pi_step) probe_step); auto.
  - intros x y; rewrite weak_star_flip; compute; apply weaken_pi.
  - apply weaken_probe.
  - compute; intros x y z xy yz.
    destruct yz.
    exists (x * TOP); repeat split; auto.
    apply (@weak_star_trans _ _ x0 x x) in xy; auto.
    rewrite <- weaken_pi in xy; auto.
Qed.

Instance commuting_pi_probe (Var : Set) : Commuting Var pi probe.
Proof.
  apply (weaken_commuting _ _ _ pi_step probe_step); auto.
  - apply weaken_pi.
  - apply weaken_probe.
  - compute; intros x y z xy yz; destruct yz; exists (x * TOP); split; auto.
    rewrite xy; reflexivity.
Qed.

(* TODO try to replace this with commuting_beta_step_pi
   since [beta TOP x -> x == TOP]? *)
Lemma beta_step_pi_top (Var : Set) (x y : Code Var) :
  beta_step x y -> (pi x TOP <-> pi y TOP).
Proof.
  intro Hb; split; intro Hp.
  - admit. (* TODO similar strategy to commuting_flip_beta_beta *)
  - rewrite Hb; auto.
Qed.

Lemma beta_pi_top (Var : Set) (x y : Code Var) :
  beta x y -> (pi x TOP <-> pi y TOP).
Proof.
  intro Hb; rewrite weaken_beta in Hb; induction Hb; try tauto.
  transitivity (pi y TOP); auto.
  apply beta_step_pi_top; auto.
Qed.

Lemma probe_pi_top (Var : Set) (x y : Code Var) :
  probe x y -> pi x TOP -> pi y TOP.
Proof.
  intro Hp; rewrite weaken_probe in Hp; induction Hp; try tauto.
  destruct H; intro H; apply IHHp.
  transitivity (TOP * TOP : Code Var); auto.
  transitivity (K * TOP * TOP : Code Var); auto.
Qed.
