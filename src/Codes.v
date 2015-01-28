(** * Combinatory algebra with parametric variables *)

Definition Succ := S%nat.  (* an alias for later *)

Require Import Coq.Program.Basics.
Require Import Coq.Setoids.Setoid.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Arith.EqNat.
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

Notation "x * y" := (code_ap x y) : code_scope.

Open Scope code_scope.
Delimit Scope code_scope with code.
Bind Scope code_scope with code.

Notation "'TOP'" := code_top : code_scope.
Notation "'BOT'" := code_bot : code_scope.
Notation "'J'" := code_j : code_scope.
Notation "'R'" := code_r : code_scope.
Notation "'I'" := code_i : code_scope.
Notation "'K'" := code_k : code_scope.
Notation "'B'" := code_b : code_scope.
Notation "'C'" := code_c : code_scope.
Notation "'S'" := code_s : code_scope.
Notation "x 'o' y" := (code_b * x * y) : code_scope.
Notation "x || y" := (code_j * x * y) : code_scope.
Notation "x (+) y" := (code_r * x * y) : code_scope.

Definition code_join {Var : Set} x y : Code Var := x || y.

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

Inductive pi {Var : Set} : Code Var -> Code Var -> Prop :=
  | pi_refl {x} : pi x x
  | pi_trans {x} y {z} : pi x y -> pi y z -> pi x z
  | pi_ap_left {x x' y} : pi x x' -> pi (x * y) (x' * y)
  | pi_ap_right {x y y'} : pi y y' -> pi (x * y) (x * y')
  | pi_top x : pi (TOP * x) TOP
  | pi_bot x : pi x BOT
  | pi_j_left {x y} : pi (x || y) x
  | pi_j_right {x y} : pi (x || y) y.

Inductive approx {Var : Set} : Code Var -> Code Var -> Prop :=
  approx_intro x y z : beta x y -> pi y z -> approx x z.

Inductive conv {Var : Set} : Code Var -> Prop :=
  | conv_approx {x} : approx x TOP -> conv x
  | conv_ap {x} : conv (x * TOP) -> conv x.

Inductive prob {Var : Set} : Code Var -> Prop :=
  | prob_top : prob TOP
  | prob_bot : prob BOT
  | prob_r p q : prob p -> prob q -> prob (p (+) q).

Inductive pconv {Var : Set} : Code Var -> Code Var -> Prop :=
  | pconv_approx {p x} : prob p -> approx x p -> pconv p x
  | pconv_ap {p x} : pconv p (x * TOP) -> pconv p x.

Hint Constructors beta.
Hint Constructors pi.
Hint Constructors approx.
Hint Constructors conv.
Hint Constructors prob.
Hint Constructors pconv.

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

Lemma beta_ap {Var : Set} {x x' y y' : Code Var} :
  beta x x' -> beta y y' -> beta (x * y) (x' * y').
Proof.
  transitivity (x' * y); auto.
Qed.

Lemma beta_confluent (Var : Set) (x y y' : Code Var) :
  beta x y -> beta x y' -> exists z, beta y z /\ beta y' z.
Proof.
Admitted.

Ltac beta_confluent x y y' xy xy' :=
  let w := fresh "w" in
  let yw := fresh y w in
  let y'w := fresh y' w in
  let H := fresh in
  set (H := beta_confluent _ x y y' xy xy');
  destruct H as [w [yw y'w]].

Instance pi_transitive (Var : Set) : Transitive (@pi Var).
Proof.
  intros x y z Hxy Hyz; apply pi_trans with y; auto.
Qed.

Instance pi_reflexive (Var : Set) : Reflexive (@pi Var).
Proof. auto. Qed.

Instance pi_preorder (Var : Set) : PreOrder (@pi Var).
Proof.
  split; [apply pi_reflexive | apply pi_transitive].
Qed.

Instance code_ap_pi (Var : Set) : Proper (pi ++> pi ++> pi) (@code_ap Var).
Proof.
  intros x x' Hx y y' Hy; transitivity (x * y'); auto.
Qed.

Lemma pi_beta_to_beta_pi (Var : Set) (x y z : Code Var) :
  pi x y -> beta y z -> exists y', beta x y' /\ pi y' z.
Proof.
  intros Hp; generalize z as w; clear z; induction Hp; intros z' Hb; eauto.
  (* TODO this requires a confluence-like argument. *)
Admitted.

Ltac pi_beta_to_beta_pi x y z xy yz :=
  let w := fresh y "_" in
  let xw := fresh x w in
  let wz := fresh w z in
  let H := fresh in
  set (H := pi_beta_to_beta_pi _ x y z xy yz);
  destruct H as [w [xw wz]].

Lemma beta_pi_confluent (Var : Set) (x y y' : Code Var) :
  beta x y -> pi x y' -> exists z, pi y z /\ beta y' z.
Proof.
Admitted.

Ltac beta_pi_confluent x y y' xy xy' :=
  let w := fresh "w" in
  let yw := fresh y w in
  let y'w := fresh y' w in
  let H := fresh in
  set (H := beta_pi_confluent _ x y y' xy xy');
  destruct H as [w [yw y'w]].

Instance approx_transitive (Var : Set) : Transitive (@approx Var).
Proof.
  unfold Transitive; intros x y z Hxy Hyz.
  destruct Hxy as [x u y xu uy].
  destruct Hyz as [y v z yv vz].
  pi_beta_to_beta_pi u y v uy yv.
  apply approx_intro with y_.
  transitivity u; auto.
  apply pi_trans with v; auto.
Qed.

Instance approx_reflexive (Var : Set) : Reflexive (@approx Var).
Proof.
  unfold Reflexive; intro x; apply approx_intro with x; auto.
Qed.

Instance approx_preorder (Var : Set) : PreOrder (@approx Var).
Proof.
  split; [apply approx_reflexive | apply approx_transitive].
Qed.

Instance approx_beta (Var : Set) :
  Proper (beta --> beta ++> impl) (@approx Var).
Proof.
  intros x x' xx' z z' zz' xyz.
  destruct xyz as [x y z xy yz].
  pi_beta_to_beta_pi y z z' yz zz'.
  apply approx_intro with z_; auto.
  transitivity x; auto.
  transitivity y; auto.
Qed.

(* Is this needed?
Instance approx_beta' (Var : Set) :
  Proper (beta ++> beta --> impl) (@approx Var).
Proof.
  compute; intros x x' xx' z z' zz' xyz.
  destruct xyz as [x y z xy yz].
  beta_confluent x x' y xx' xy.
  beta_pi_confluent y w z yw yz.
  apply approx_intro with ; auto.
  transitivity w0; auto.
  transitivity w0; auto.
Qed.
*)

Instance approx_pi (Var : Set) : Proper (pi --> pi ++> impl) (@approx Var).
Proof.
  intros x x' xx' z z' zz' Ha; destruct Ha as [x y z xy yz].
  set (wHw := pi_beta_to_beta_pi _ x' x y xx' xy); destruct wHw as [w [xw wy]].
  apply approx_intro with w; auto.
  transitivity y; auto.
  transitivity z; auto.
Qed.

Instance approx_beta_pi (Var : Set) :
  Proper (beta --> pi ++> impl) (@approx Var).
Proof.
  intros x x' Hx z z' Hz Ha; destruct Ha as [x y z xy yz].
  apply approx_intro with y.
    transitivity x; auto.
  transitivity z; auto.
Qed.

Instance code_ap_approx (Var : Set) :
  Proper (approx ++> approx ++> approx) (@code_ap Var).
Proof.
  intros x z xz x' z' x'z'.
  destruct xz as [x y z xy yz];  rewrite xy; rewrite yz;
  destruct x'z' as [x' y' z' x'y' y'z']; rewrite x'y'; rewrite y'z';
  reflexivity.
Qed.

Lemma conv_top (Var : Set) : conv (TOP : Code Var).
Proof. eauto. Qed.
Hint Resolve conv_top.

Lemma not_conv_bot (Var : Set) : ~ conv (BOT : Code Var).
Proof.
Admitted.
Hint Resolve not_conv_bot.

Instance conv_beta (Var : Set) : Proper (beta ==> iff) (@conv Var).
Proof.
  intros x x' xx'; split.
    intros Hc; induction Hc; apply conv_approx; admit.
  intros Hc; induction Hc; apply conv_approx; rewrite xx'; auto.
Admitted.

Instance conv_pi (Var : Set) : Proper (pi --> impl) (@conv Var).
Proof.
  compute; intros x x' xx' Ha.
Admitted.

Instance conv_proper_approx (Var : Set) : Proper (approx --> impl) (@conv Var).
Proof.
  intros x z Hxz Hc.
  destruct Hxz as [x y z Hxy Hyz].
  rewrite Hxy; rewrite Hyz; auto.
Qed.

(** ** Substitution *)

Fixpoint code_sub {Var Var' : Set}
  (f : Var -> Code Var') (x : Code Var) : Code Var' :=
  match x with
  | code_var v => f v
  | l * r => (code_sub f l) * (code_sub f r)
  | TOP => TOP
  | BOT => BOT
  | J => J
  | R => R
  | I => I
  | K => K
  | B => B
  | C => C
  | S => S
  end.

Notation "x @ f" := (code_sub f x) : code_scope.

Lemma var_monad_unit_right (Var : Set) (x : Code Var) : x @ code_var = x.
Proof.
  induction x; auto.
  unfold code_sub; fold (@code_sub Var Var).
  rewrite IHx1; rewrite IHx2; auto.
Qed.
Hint Rewrite var_monad_unit_right : code_simpl.

Lemma var_monad_unit_left (Var Var' : Set) (f : Var -> Code Var') x :
  (code_var x) @ f = f x.
Proof.
  compute; auto.
Qed.
Hint Rewrite var_monad_unit_left : code_simpl.

Lemma code_sub_ap (Var Var' : Set)
  (x y : Code Var) (f : Var -> Code Var') : (x * y @ f) = (x @ f) * (y @ f).
Proof.
  simpl; auto.
Qed.
Hint Rewrite code_sub_ap : code_simpl.

Lemma var_monad_assoc
  (Var Var' Var'' : Set)
  (f : Var -> Code Var')
  (g : Var' -> Code Var'')
  (x : Code Var) :
  (x @ f) @ g = x @ (fun v => (f v) @ g).
Proof.
  induction x; auto.
  repeat rewrite code_sub_ap.
  rewrite IHx1; rewrite IHx2; auto.
Qed.
Hint Rewrite var_monad_assoc : code_simpl.

Lemma code_sub_ext (Var Var' : Set)
  (f g : Var -> Code Var') (fg : forall v, f v = g v) x :
  x @ f = x @ g.
Proof.
  induction x; simpl; auto.
  rewrite IHx1; rewrite IHx2; auto.
Qed.

Lemma code_sub_beta_left (Var Var' : Set)
  (f g : Var -> Code Var') (fg : forall v, beta (f v) (g v))
  (x : Code Var) : beta (x @ f) (x @ g).
Proof.
  induction x; auto.
    compute; auto.
  unfold code_sub; fold (@code_sub Var Var').
  transitivity ((x1 @ g) * (x2 @ f)); auto.
Qed.
Hint Resolve code_sub_beta_left.

Lemma code_sub_beta_right (Var Var' : Set)
  (f : Var -> Code Var') (x y : Code Var)
  (xy : beta x y) : beta (x @ f) (y @ f).
Proof.
  induction xy; repeat rewrite code_sub_ap; simpl; auto.
  transitivity (y @ f); auto.
Qed.
Hint Resolve code_sub_beta_right.

Instance code_sub_beta (Var Var' : Set) :
  Proper ((eq ==> beta) ==> beta ==> beta) (@code_sub Var Var').
Proof.
  intros f g Hfg x y Hxy; transitivity (y @ f);
  [apply code_sub_beta_right | apply code_sub_beta_left]; auto.
Qed.

Lemma code_sub_pi_left (Var Var' : Set)
  (f g : Var -> Code Var') (fg : forall v, pi (f v) (g v))
  (x : Code Var) : pi (x @ f) (x @ g).
Proof.
  induction x; auto.
    compute; auto.
  unfold code_sub; fold (@code_sub Var Var').
  rewrite IHx1; rewrite IHx2; auto.
Qed.
Hint Resolve code_sub_pi_left.

Lemma code_sub_pi_right (Var Var' : Set)
  (f : Var -> Code Var') (x y : Code Var)
  (xy : pi x y) : pi (x @ f) (y @ f).
Proof.
  induction xy; repeat rewrite code_sub_ap; simpl; auto.
  transitivity (y @ f); auto.
Qed.
Hint Resolve code_sub_pi_right.

Instance code_sub_pi (Var Var' : Set) :
  Proper ((eq ==> pi) ==> pi ==> pi) (@code_sub Var Var').
Proof.
  intros f g Hfg x y Hxy; transitivity (y @ f);
  [apply code_sub_pi_right | apply code_sub_pi_left]; auto.
Qed.

Lemma code_sub_approx_right (Var Var' : Set)
  (f : Var -> Code Var') (x y : Code Var)
  (xy : approx x y) : approx (x @ f) (y @ f).
Proof.
  induction xy; repeat rewrite code_sub_ap; simpl; auto.
  apply approx_intro with (y @ f); auto.
Qed.
Hint Resolve code_sub_approx_right.

Lemma code_sub_approx_left (Var Var' : Set)
  (f g : Var -> Code Var') (fg : forall v, approx (f v) (g v))
  (x : Code Var) : approx (x @ f) (x @ g).
Proof.
  induction x; try (compute ; reflexivity).
    compute; auto.
  unfold code_sub; fold (@code_sub Var Var').
  rewrite IHx1; rewrite IHx2; reflexivity.
Qed.
Hint Resolve code_sub_approx_left.

Instance code_sub_approx (Var Var' : Set) :
  Proper ((eq ==> approx) ==> approx ==> approx) (@code_sub Var Var').
Proof.
  intros f h fh x z xz.
  transitivity (x @ h); auto.
Qed.
