(** * Reduction relations *)

Require Import Coq.Program.Basics.
Require Import Coq.Program.Equality.
Require Import Coq.Setoids.Setoid.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Export Substitution.

Inductive star {Var : Set} (r : relation (Term Var)) : relation (Term Var) :=
  | star_step {x y} : r x y -> star r x y
  | star_refl {x} : star r x x
  | star_trans {x} y {z} : star r x y -> star r y z -> star r x z.
Hint Constructors star.

Inductive weak_star
  {Var : Set} (r : relation (Term Var)) : relation (Term Var) :=
  | weak_star_refl {x} : weak_star r x x
  | weak_star_trans {x} y {z} : r x y -> weak_star r y z -> weak_star r x z.
Hint Constructors weak_star.

Lemma weaken_star (Var : Set) (r : relation (Term Var)) (x y : Term Var) :
  star r x y <-> weak_star r x y.
Proof.
  split; intro H; induction H; eauto.
  clear H H0; induction IHstar1; auto.
  apply weak_star_trans with y; auto.
Qed.

Lemma weak_star_flip (Var : Set) (r : relation (Term Var)) (x y : Term Var) :
  weak_star (flip r) x y <-> weak_star r y x.
Proof.
  repeat rewrite <- weaken_star.
  split; intro H; induction H; eauto.
Qed.


Inductive probe: forall (Var Var': Set), Term Var -> Term Var' -> Prop :=
  | probe_refl {Var x} : probe Var Var x x
  | probe_trans {Var x} Var' y {Var'' z} :
      probe Var Var' x y -> probe Var' Var'' y z -> probe Var Var'' x z
  | probe_top {Var x} : probe Var Var x (x * TOP)
  | probe_lambda {Var x} : probe (option' Var) Var x (LAMBDA x).
Hint Constructors probe.

Inductive probe_step : forall (Var Var' : Set), Term Var -> Term Var' -> Prop :=
  | probe_step_top {Var x} : probe_step Var Var x (x * TOP)
  | probe_step_lambda {Var x} :
      probe_step (option' Var) Var x (LAMBDA x).
Hint Constructors probe_step.

(* Coq does not support heterogeneous relations as nicely as homogeneous. *)
(* Probe could be weakened further by requiring lambdas precede tops. *)
Lemma weaken_probe (Var : Set) (x y : Term Var) :
  probe Var Var x y <-> weak_star probe_step x y.
Proof.
  rewrite <- weaken_star.
  split; intro H; induction H; eauto.
  inversion H; auto.
Qed.

(* OLD large-step
Definition none_sub {Var : Set} (x : Term Var) (v : option Var) : Term Var :=
  match v with
  | None => x
  | Some v' => VAR v'
  end.

Definition lambda_app_sub {Var : Set} (x : Term (option Var)) (y : Term Var) :
  Term Var := x @ (none_sub y).
*)

Inductive protect {Var : set} : Term Var -> Term (option Var) -> Prop :=
  | protect_top : protect TOP TOP
  | protect_bot : protect BOT BOT
  | protect_join {x x' y y'} :
      protect x x' -> protect y y' -> protect (x || y) (x' || y')
  | protect_rand {x x' y y'} :
      protect x x' -> protect y y' -> protect (x (+) y) (x' (+) y')
  | protect_app {x x' y y'} :
      protect x x' -> protect y y' -> protect (x * y) (x' * y')
  | protect_var {v} : protect (VAR v) (VAR (Some v))
  | protect_lambda {x} : protect (LAMBDA x) TOP (* TODO *).

Inductive sub_step {Var : Set} : relation (Term Var) :=
  | sub_step_top {x} : sub_step (LAMBDA TOP * x) TOP
  | sub_step_bot {x} : sub_step (LAMBDA BOT * x) BOT
  | sub_step_join {f1 f2 x} :
      sub_step (LAMBDA (f1 || f2) * x) ((LAMBDA f1 * x) || (LAMBDA f2 * x))
  | sub_step_rand {f1 f2 x} :
      sub_step (LAMBDA (f1 || f2) * x) ((LAMBDA f1 * x) (+) (LAMBDA f2 * x))
  | sub_step_app {f1 f2 x} :
      sub_step (LAMBDA (f1 * f2) * x) ((LAMBDA f1 * x) * (LAMBDA f2 * x))
  | sub_step_var_none {v x} : sub_step (LAMBDA (VAR None) * x) x
  | sub_step_var_some {v x} : sub_step (LAMBDA (VAR (Some v)) * x) (VAR v)
  | sub_step_lambda {f x x'} :
      protect x x' ->
      sub_step (LAMBDA (LAMBDA f) * x) (LAMBDA (LAMBDA f * x')).

Inductive beta {Var : Set} : relation (Term Var) :=
  | beta_refl {x} : beta x x
  | beta_trans {x} y {z} : beta x y -> beta y z -> beta x z
  | beta_app_left {x x' y} : beta x x' -> beta (x * y) (x' * y)
  | beta_app_right {x y y'} : beta y y' -> beta (x * y) (x * y')
  | beta_join_left {x x' y} : beta x x' -> beta (x || y) (x' || y)
  | beta_join_right {x y y'} : beta y y' -> beta (x || y) (x || y')
  | beta_rand_left {x x' y} : beta x x' -> beta (x (+) y) (x' (+) y)
  | beta_rand_right {x y y'} : beta y y' -> beta (x (+) y) (x (+) y')
  | beta_lambda {x x'} :
      @beta (option Var) x x' -> beta (LAMBDA x) (LAMBDA x')
  (* OLD large step
  | beta_sub {x y} : beta (LAMBDA x * y) (lambda_app_sub x y)
  *)
  | beta_sub {x y z} : sub_step (LAMBDA x * y) z -> beta (LAMBDA x * y) z
  | beta_j_ap {x y z} : beta ((x || y) * z) (x * z || y * z)
  | beta_r_ap {x y z} : beta ((x (+) y) * z) (x * z (+) y * z)
  | beta_r_idem {x} : beta (x (+) x) x
  | beta_r_sym {x y} : beta (x (+) y) (y (+) x)
  | beta_r_sym_sym {w x y z} :
      beta ((w(+)x) (+) (y(+)z)) ((x(+)y) (+) (z(+)w)).
Hint Constructors beta.

Inductive beta_step {Var : Set} : relation (Term Var) :=
  | beta_step_app_left {x x' y} : beta_step x x' -> beta_step (x * y) (x' * y)
  | beta_step_app_right {x y y'} : beta_step y y' -> beta_step (x * y) (x * y')
  | beta_step_join_left {x x' y} :
      beta_step x x' -> beta_step (x || y) (x' || y)
  | beta_step_join_right {x y y'} :
      beta_step y y' -> beta_step (x || y) (x || y')
  | beta_step_rand_left {x x' y} :
      beta_step x x' -> beta_step (x (+) y) (x' (+) y)
  | beta_step_rand_right {x y y'} :
      beta_step y y' -> beta_step (x (+) y) (x (+) y')
  | beta_step_lambda {x x'} :
      @beta_step (option Var) x x' -> beta_step (LAMBDA x) (LAMBDA x')
  | beta_step_sub {x y} : beta_step (LAMBDA x * y) (lambda_app_sub x y)
  | beta_step_j_ap {x y z} : beta_step ((x || y) * z) (x * z || y * z)
  | beta_step_r_ap {x y z} : beta_step ((x (+) y) * z) (x * z (+) y * z)
  | beta_step_r_idem {x} : beta_step (x (+) x) x
  | beta_step_r_sym {x y} : beta_step (x (+) y) (y (+) x)
  | beta_step_r_sym_sym {w x y z} :
      beta_step ((w(+)x) (+) (y(+)z)) ((x(+)y) (+) (z(+)w)).
Hint Constructors beta_step.

Lemma weaken_beta (Var : Set) (x y : Term Var) :
  beta x y <-> weak_star beta_step x y.
Proof.
  rewrite <- weaken_star.
  split; intro H; induction H; eauto;
  match goal with
  | [IH : star _ _ _ |- star _ _ _ ] => clear H; induction IH; eauto
  | _ => induction H; auto
  end.
Qed.


Inductive pi {Var : Set} : relation (Term Var) :=
  | pi_refl {x} : pi x x
  | pi_trans {x} y {z} : pi x y -> pi y z -> pi x z
  | pi_app_left {x x' y} : pi x x' -> pi (x * y) (x' * y)
  | pi_app_right {x y y'} : pi y y' -> pi (x * y) (x * y')
  | pi_join_left {x x' y} : pi x x' -> pi (x || y) (x' || y)
  | pi_join_right {x y y'} : pi y y' -> pi (x || y) (x || y')
  | pi_rand_left {x x' y} : pi x x' -> pi (x (+) y) (x' (+) y)
  | pi_rand_right {x y y'} : pi y y' -> pi (x (+) y) (x (+) y')
  | pi_lambda {x x'} : @pi (option Var) x x' -> pi (LAMBDA x) (LAMBDA x')
  | pi_sub {x y} : pi (LAMBDA x * y) (lambda_app_sub x y)
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

Inductive pi_step {Var : Set} : relation (Term Var) :=
  | pi_step_app_left {x x' y} : pi_step x x' -> pi_step (x * y) (x' * y)
  | pi_step_app_right {x y y'} : pi_step y y' -> pi_step (x * y) (x * y')
  | pi_step_join_left {x x' y} : pi_step x x' -> pi_step (x || y) (x' || y)
  | pi_step_join_right {x y y'} : pi_step y y' -> pi_step (x || y) (x || y')
  | pi_step_rand_left {x x' y} : pi_step x x' -> pi_step (x (+) y) (x' (+) y)
  | pi_step_rand_right {x y y'} : pi_step y y' -> pi_step (x (+) y) (x (+) y')
  | pi_step_lambda {x x'} :
      @pi_step (option Var) x x' -> pi_step (LAMBDA x) (LAMBDA x')
  | pi_step_sub {x y} : pi_step (LAMBDA x * y) (lambda_app_sub x y)
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

Lemma weaken_pi (Var : Set) (x y : Term Var) :
  pi x y <-> weak_star pi_step x y.
Proof.
  rewrite <- weaken_star.
  split; intro H; induction H; eauto;
  match goal with
  | [IH : star _ _ _ |- star _ _ _ ] => clear H; induction IH; eauto
  | _ => induction H; auto
  end.
Qed.


Hint Rewrite @beta_j_ap @beta_r_ap @beta_r_idem : beta_safe.
Hint Rewrite @beta_sub : beta_unsafe.

Tactic Notation "beta_simpl" :=
  autorewrite with term_simpl beta_safe.
Tactic Notation "beta_simpl" "in" hyp(H) :=
  autorewrite with term_simpl beta_safe in H.
Tactic Notation "beta_reduce" :=
  autorewrite with term_simpl beta_safe beta_unsafe.
Tactic Notation "beta_reduce" "in" hyp(H) :=
  autorewrite with term_simpl beta_safe beta_unsafe in H.

(** To avoid nontermination in [beta_reduce],
    we provide a mechanism to "freeze" terms during reduction. *)
Tactic Notation "freeze" reference(c) "in" tactic(tac) :=
  let v := fresh "v" in
  let H := fresh "Hv" in
  assert (exists v, c=v) as H;
  [ exists c; reflexivity
  | destruct H as [v H]; rewrite H; tac; destruct H].


Class Commuting (Var : Set) (r s : relation (Term Var)) :=
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

Lemma weaken_commuting (Var : Set) (r s r' s' : relation (Term Var)) :
  (forall (x y : Term Var), r x y <-> weak_star r' x y) ->
  (forall (x y : Term Var), s x y <-> weak_star s' x y) ->
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

Lemma probe_step_probe (Var : Set) (x y : Term Var) :
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
  (@subrelation (Term Var)) beta_step beta.
Proof.
  intros x y H; induction H; eauto.
Qed.

Instance APP_beta (Var : Set) :
  Proper (beta ==> beta ==> beta) (@APP Var).
Proof.
  intros x x' Hx y y' Hy; transitivity (x * y'); auto.
Qed.

Ltac simpl_beta_step :=
  (* repeat *)
  match goal with
    | [H : beta_step _ _ |- _] => induction H
    | [H : beta_step ?x ?x -> _ |- _] => clear H
  end.

Lemma beta_step_beta (Var : Set) (x y : Term Var) :
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
    (* TODO try induction over just one variable,
       mapping beta to beta.
       The only problem is with steps that are the same (use refl)
       and in beta_r_ when redexes intersect.
       Try to write a tactic matching against beta constructors. *)
    (* OLD
    induction xy; induction yz; auto.
    *)
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
  (@subrelation (Term Var)) pi_step pi.
Proof.
  intros x y H; induction H; eauto.
Qed.

Instance beta_step_pi_subrelation (Var : Set) :
  (@subrelation (Term Var)) beta_step pi.
Proof.
  intros x y H; induction H; eauto.
Qed.

Instance beta_pi_subrelation (Var : Set) : (@subrelation (Term Var)) beta pi.
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

Instance APP_pi (Var : Set) :
  Proper (pi ==> pi ==> pi) (@APP Var).
Proof.
  intros x x' Hx y y' Hy; transitivity (x * y'); auto.
Qed.

Ltac simpl_pi_step :=
  (* repeat *)
  match goal with
    | [H : pi_step _ _ |- _] => induction H
    | [H : pi_step ?x ?x -> _ |- _] => clear H
  end.

Lemma pi_step_pi (Var : Set) (x y : Term Var) :
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
    (* TODO similar to commuting_flip_beta_beta *)
    (* OLD
    induction xy; induction yz; auto.
    *)
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
Lemma beta_step_pi_top (Var : Set) (x y : Term Var) :
  beta_step x y -> (pi x TOP <-> pi y TOP).
Proof.
  intro Hb; split; intro Hp.
  - admit. (* TODO similar strategy to commuting_flip_beta_beta *)
  - rewrite Hb; auto.
Qed.

Lemma beta_pi_top (Var : Set) (x y : Term Var) :
  beta x y -> (pi x TOP <-> pi y TOP).
Proof.
  intro Hb; rewrite weaken_beta in Hb; induction Hb; try tauto.
  transitivity (pi y TOP); auto.
  apply beta_step_pi_top; auto.
Qed.

Lemma probe_pi_top (Var : Set) (x y : Term Var) :
  probe x y -> pi x TOP -> pi y TOP.
Proof.
  intro Hp; rewrite weaken_probe in Hp; induction Hp; try tauto.
  destruct H; intro H; apply IHHp.
  transitivity (TOP * TOP : Term Var); auto.
  transitivity (K * TOP * TOP : Term Var); auto.
  unfold K.
  rewrite beta_sub; compute.
  rewrite beta_sub; compute.
  auto.
Qed.

(** ** Reduction and substitution *)

Lemma term_sub_proper_probe (Var Var' : Set)
  (f : Var -> Term Var') (x y : Term Var) :
  probe x y -> probe (x @ f) (y @ f).
Proof.
  intro xy; induction xy; simpl.
  - reflexivity.
  - transitivity (y @ f); auto.
  - apply probe_top; auto.
Qed.

Instance term_map_proper_beta (Var Var' : Set) :
  Proper (eq ==> beta ==> beta) (@term_map Var Var').
Proof.
  intros f f' ff' x x' xx'; rewrite <- ff'; clear f' ff'.
  revert Var' f; induction xx'; intros Var' f; simpl; auto.
  - transitivity (term_map f y); auto.
  - rewrite beta_sub.
    admit.
    (*
    dependent induction x; simpl; auto.
    *)
Qed.

Instance some_sub_proper_beta (Var Var' : Set) :
  Proper ((eq ==> beta) ==> eq ==> beta) (@some_sub Var Var').
Proof.
  intros f f' ff'; compute in ff'.
  intros v v' vv'; rewrite <- vv'; clear v' vv'.
  case_eq v; auto.
  intros v' vv'; simpl; rewrite ff'; reflexivity.
Qed.

Lemma some_sub_beta 
  (Var Var' : Set) (f g : Var -> Term Var') :
  (forall v, beta (f v) (g v)) ->
  forall v, beta (some_sub f v) (some_sub g v).
Proof.
  intros Hb v; case_eq v; auto.
  intros v' vv'; simpl; rewrite Hb; reflexivity.
Qed.

Lemma term_sub_beta_left
  (Var Var' : Set) (f g : Var -> Term Var') (x : Term Var) :
  (forall v, beta (f v) (g v)) -> beta (x @ f) (x @ g).
Proof.
  revert Var' f g; induction x; intros Var' f g fg; auto.
  - simpl; transitivity ((x1 @ g) || (x2 @ f)); auto.
  - simpl; transitivity ((x1 @ g) (+) (x2 @ f)); auto.
  - simpl; transitivity ((x1 @ g) * (x2 @ f)); auto.
  - simpl; auto.
  - simpl; apply beta_lambda.
    rewrite (IHx (option Var') (some_sub f) (some_sub g)); clear IHx;
    intros; auto.
    apply ext_respectful in fg; rewrite fg; reflexivity.
Qed.
Hint Resolve term_sub_beta_left.

Lemma lambda_app_sub_sub
  (Var : Set) (y : Term Var) (x : Term (option Var))
  (Var' : Set) (f : Var -> Term Var') :
  lambda_app_sub x y @ f = lambda_app_sub (x @ some_sub f) (y @ f).
Proof.
  revert Var' f.
  dependent induction x; intros; try (simpl; auto; reflexivity).
Admitted.

Lemma term_sub_beta_right
  (Var Var' : Set) (f : Var -> Term Var') (x y : Term Var) :
  beta x y -> beta (x @ f) (y @ f).
Proof.
  intro xy; revert Var' f; induction xy; intros Var' f;
  try (simpl; auto; reflexivity).
  - transitivity (y @ f); auto.
  - simpl; rewrite beta_sub, lambda_app_sub_sub; reflexivity.
Qed.
Hint Resolve term_sub_beta_right.

Instance term_sub_proper_beta (Var Var' : Set) :
  Proper ((eq ==> beta) ==> beta ==> beta) (@term_sub Var Var').
Proof.
  intros f g Hfg x y Hxy; transitivity (y @ f);
  [apply term_sub_beta_right | apply term_sub_beta_left]; auto.
Qed.

Lemma term_sub_pi_left
  (Var Var' : Set) (f g : Var -> Term Var') (x : Term Var) :
  (forall v, pi (f v) (g v)) -> pi (x @ f) (x @ g).
Proof.
  revert Var' f g; induction x; intros Var' f g fg; auto.
  - simpl; transitivity ((x1 @ f) || (x2 @ g)); auto.
  - simpl; transitivity ((x1 @ f) (+) (x2 @ g)); auto.
  - simpl; transitivity ((x1 @ f) * (x2 @ g)); auto.
  - simpl; auto.
  - simpl; apply pi_lambda.
    rewrite (IHx (option Var') (some_sub f) (some_sub g)); clear IHx;
    intros; auto.
    admit.
    (* TODO add Instance Proper for sub parts
    apply ext_respectful in fg; rewrite fg; reflexivity.
    *)
Qed.
Hint Resolve term_sub_pi_left.

Lemma term_sub_pi_right
  (Var Var' : Set) (f : Var -> Term Var') (x y : Term Var) :
  pi x y -> pi (x @ f) (y @ f).
Proof.
  intro xy; induction xy; repeat rewrite term_sub_ap; simpl; auto.
  - transitivity (y @ f); auto.
  - admit.
  - admit.
Qed.
Hint Resolve term_sub_pi_right.

Instance term_sub_proper_pi (Var Var' : Set) :
  Proper ((eq ==> pi) ==> pi ==> pi) (@term_sub Var Var').
Proof.
  intros f g Hfg x y Hxy; transitivity (y @ f);
  [apply term_sub_pi_right | apply term_sub_pi_left]; auto.
Qed.

(** ** Reduction and closing terms *)

Instance term_close_proper_beta (Var : Set) :
  Proper (beta ==> beta) (@close Var).
Proof.
  intros x x' xx'; apply weaken_beta in xx'; induction xx'; auto.
  revert z xx' IHxx'; induction H; intros;
  try (compute; term_simpl; eauto; reflexivity).
  - unfold close; simpl.
    admit.
  - unfold close in *; simpl.
    rewrite beta_sub.
    unfold lambda_app_sub in *.
    admit.
Qed.

Instance term_close_proper_pi (Var : Set) :
  Proper (pi ==> pi) (@close Var).
Proof.
  intros x x' xx'; apply weaken_pi in xx'; induction xx'; auto.
  revert z xx' IHxx'; induction H; intros;
  try (compute; term_simpl; eauto; reflexivity).
  - admit.
  - admit.
Qed.

Lemma probe_step_close (Var : Set) (x y : Term Var) :
  probe_step x y -> probe (close x) (close y).
Proof.
  intro Hb; induction Hb; compute; auto.
Qed.

Lemma probe_close (Var : Set) (x y : Term Var) :
  probe x y -> probe (close x) (close y).
Proof.
  intro Hb; rewrite weaken_probe in Hb; induction Hb; auto.
  rewrite <- IHHb; clear Hb IHHb; auto using probe_step_close.
Qed.

Lemma beta_step_close (Var : Set) (x y : Term Var) :
  beta_step x y -> beta (close x) (close y).
Proof.
  intro Hb; induction Hb; try (compute; beta_reduce; auto).
  - admit.
  - admit.
Qed.

Lemma beta_close (Var : Set) (x y : Term Var) :
  beta x y -> beta (close x) (close y).
Proof.
  intro Hb; rewrite weaken_beta in Hb; induction Hb; auto.
  rewrite <- IHHb; clear Hb IHHb; auto using beta_step_close.
Qed.

Lemma pi_step_close (Var : Set) (x y : Term Var) :
  pi_step x y -> pi (close x) (close y).
Proof.
  intro Hb; induction Hb; try (compute; beta_reduce; auto).
  - admit.
  - admit.
Qed.

Lemma pi_close (Var : Set) (x y : Term Var) :
  pi x y -> pi (close x) (close y).
Proof.
  intro Hb; rewrite weaken_pi in Hb; induction Hb; auto.
  rewrite <- IHHb; clear Hb IHHb; auto using pi_step_close.
Qed.
