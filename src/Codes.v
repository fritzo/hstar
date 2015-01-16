(** * Combinatory algebra with parametric variables *)

Require Import Coq.Program.Basics.
Require Import Coq.Setoids.Setoid.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Classes.Morphisms_Prop.
Require Import Coq.Arith.EqNat.
Require Export Notations.

Definition Succ := S%nat. (* an alias for later *)

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
  | code_s : code
  | code_y : code
  | code_v : code.
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
Notation "'Y'" := code_y : code_scope.
Notation "'V'" := code_v : code_scope.
Notation "x 'o' y" := (code_b * x * y)%code : code_scope.
Notation "x || y" := (code_j * x * y)%code : code_scope.
Notation "x (+) y" := (code_r * x * y)%code : code_scope.

Definition code_join {Var : Set} x y : Code Var := x || y.

Inductive beta {Var : Set} : Code Var -> Code Var -> Prop :=
  | beta_refl {x} : beta x x
  | beta_sym {x y} : beta x y -> beta y x
  | beta_trans {x} y {z} : beta x y -> beta y z -> beta x z
  | beta_ap_left {x x' y} : beta x x' -> beta (x * y) (x' * y)
  | beta_ap_right {x y y'} : beta y y' -> beta (x * y) (x * y')
  | beta_i {x} : beta (I * x) x
  | beta_k {x y} : beta (K * x * y) x
  | beta_b {x y z} : beta (B * x * y * z) (x * (y * z))
  | beta_c {x y z} : beta (C * x * y * z) (x * z * y)
  | beta_s {x y z} : beta (S * x * y * z) (x * z * (y * z))
  | beta_y {x} : beta (Y * x) (x * (Y * x))
  | beta_v {x} : beta (V * x) (I || x o (V * x))
  | beta_j_ap {x y z} : beta ((x || y) * z) (x * z || y * z)
  | beta_r_ap {x y z} : beta ((x (+) y) * z) (x * z (+) y * z)
  | beta_r_idem {x} : beta (x (+) x) x
  | beta_r_sym {x y} : beta (x (+) y) (y (+) x)
  | beta_r_sym_sym {w x y z} : beta ((w(+)x) (+) (y(+)z))
                                  ((x(+)y) (+) (z(+)w)).

Inductive pi {Var : Set} : Code Var -> Code Var -> Prop :=
  | pi_refl {x} : pi x x
  | pi_trans {x} y {z} : pi x y -> pi y z -> pi x z
  | pi_ap_left {x x' y} : pi x x' -> pi (x * y) (x' * y)
  | pi_ap_right {x y y'} : pi y y' -> pi (x * y) (x * y')
  | pi_top x : pi TOP x
  | pi_bot x : pi x BOT
  | pi_j_left {x y} : pi (x || y) x
  | pi_j_right {x y} : pi (x || y) y.

Inductive approx {Var : Set} : Code Var -> Code Var -> Prop :=
  approx_intro x y z : beta x y -> pi y z -> approx x z.

Hint Constructors beta.
Hint Constructors pi.
Hint Constructors approx.

Definition Beta_i (Var : Set) := (@beta_i Var).
Definition Beta_k (Var : Set) := (@beta_k Var).
Definition Beta_b (Var : Set) := (@beta_b Var).
Definition Beta_c (Var : Set) := (@beta_c Var).
Definition Beta_s (Var : Set) := (@beta_s Var).
Definition Beta_y (Var : Set) := (@beta_y Var).
Definition Beta_v (Var : Set) := (@beta_v Var).
Definition Beta_j_ap (Var : Set) := (@beta_j_ap Var).
Definition Beta_r_ap (Var : Set) := (@beta_r_ap Var).
Definition Beta_r_idem (Var : Set) := (@beta_r_idem Var).

Hint Rewrite Beta_i Beta_k Beta_b Beta_c Beta_j_ap Beta_r_ap Beta_r_idem
  : beta_safe.
Hint Rewrite Beta_s Beta_y Beta_v
  : beta_unsafe.

Tactic Notation "beta_simpl" := autorewrite with beta_safe.
Tactic Notation "beta_simpl" "in" hyp(H) := autorewrite with beta_safe in H.
Tactic Notation "beta_reduce" := autorewrite with beta_safe beta_unsafe.
Tactic Notation "beta_reduce" "in" hyp(H) :=
  autorewrite with beta_safe beta_unsafe in H.
Tactic Notation "code_simpl" := autorewrite with beta_safe code_simpl.
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

Instance beta_reflexive (Var : Set) : Reflexive (@beta Var).
Proof. auto. Qed.

Instance beta_symmetric (Var : Set) : Symmetric (@beta Var).
Proof. auto. Qed.

Instance beta_transitive (Var : Set) : Transitive (@beta Var).
Proof.
  unfold Transitive; intros x y z; apply beta_trans.
Qed.

Instance beta_equivalence (Var : Set) : Equivalence (@beta Var).
Proof.
  split; [apply beta_reflexive | apply beta_symmetric | apply beta_transitive].
Qed.

Instance code_ap_beta (Var : Set) :
  Proper (beta ==> beta ==> beta) (@code_ap Var).
Proof.
  compute; intros x x' Hx y y' Hy.
  transitivity (x * y'); auto.
Qed.

Instance pi_transitive (Var : Set) : Transitive (@pi Var).
Proof.
  unfold Transitive; intros x y z Hxy Hyz; apply pi_trans with y; auto.
Qed.

Instance pi_reflexive (Var : Set) : Reflexive (@pi Var).
Proof. auto. Qed.

Instance pi_preorder (Var : Set) : PreOrder (@pi Var).
Proof.
  split; [apply pi_reflexive | apply pi_transitive].
Qed.

Instance code_ap_pi (Var : Set) : Proper (pi ++> pi ++> pi) (@code_ap Var).
Proof.
  compute; intros x x' Hx y y' Hy.
  transitivity (x * y'); auto.
Qed.

Lemma pi_beta_to_beta_pi (Var : Set) (x y z : Code Var) :
  pi x y -> beta y z -> exists y', beta x y' /\ pi y' z.
Proof.
  intros Hp Hb; induction Hb; eauto.
  (* TODO this requires a confluence-like argument. *)
Admitted.

Ltac pi_beta_to_beta_pi x y z xy yz :=
  let w := fresh y "_" in
  let xw := fresh x w in
  let wz := fresh w z in
  let H := fresh in
  set (H := pi_beta_to_beta_pi _ x y z xy yz);
  destruct H as [w [xw wz]].

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

Instance approx_beta (Var : Set) : Proper (beta ==> beta ==> iff) (@approx Var).
Proof.
  compute; intros x x' xx' z z' zz'; split; intro xyz.
    destruct xyz as [x y z xy yz].
    pi_beta_to_beta_pi y z z' yz zz'.
    apply approx_intro with z_; auto.
    transitivity x; auto.
    transitivity y; auto.
  destruct xyz as [x' y' z' x'y' y'z'].
  pi_beta_to_beta_pi y' z' z y'z' (beta_sym zz').
  apply approx_intro with z'_; auto.
  transitivity x'; auto.
  transitivity y'; auto.
Qed.

Instance approx_pi (Var : Set) : Proper (pi --> pi ++> impl) (@approx Var).
Proof.
  compute; intros x x' xx' z z' zz' Ha; destruct Ha as [x y z xy yz].
  set (wHw := pi_beta_to_beta_pi _ x' x y xx' xy); destruct wHw as [w [xw wy]].
  apply approx_intro with w; auto.
  transitivity y; auto.
  transitivity z; auto.
Qed.

Instance approx_beta_pi (Var : Set) :
  Proper (beta ==> pi ==> impl) (@approx Var).
Proof.
  compute; intros x x' Hx z z' Hz Ha; destruct Ha as [x y z xy yz].
  apply approx_intro with y.
    transitivity x; auto.
  transitivity z; auto.
Qed.

Instance code_ap_approx (Var : Set) :
  Proper (approx ++> approx ++> approx) (@code_ap Var).
Proof.
  compute; intros x z xz x' z' x'z'.
  destruct xz as [x y z xy yz];  rewrite xy; rewrite yz;
  destruct x'z' as [x' y' z' x'y' y'z']; rewrite x'y'; rewrite y'z';
  reflexivity.
Qed.

Definition div {Var : Set} : Code Var := V * (C * I * TOP).

Lemma beta_div (Var : Set) (x : Code Var) :
  beta (div * x) (x || div * x * TOP).
Proof.
  unfold div.
  rewrite beta_v at 1; beta_simpl; auto.
Qed.

Definition conv {Var : Set} (x : Code Var) := approx (div * x) TOP.

Instance conv_beta (Var : Set) : Proper (beta ==> iff) (@conv Var).
Proof.
  compute; intros x x' Hx; split; intros Hc;
  inversion Hc as [u v w]; apply approx_intro with v; auto.
    rewrite <- Hx; auto.
  rewrite -> Hx; auto.
Qed.

Instance conv_pi (Var : Set) : Proper (pi --> impl) (@conv Var).
Proof.
  compute; intros x x' xx' Ha.
  rewrite xx'; auto.
Qed.

Inductive prob {Var : Set} : Code Var -> Prop :=
  | prob_top : prob TOP
  | prob_bot : prob BOT
  | prob_r p q : prob p -> prob q -> prob (p (+) q).

Definition pconv {Var : Set} (x : Code Var) (p : Code Var) :=
  approx (div * x) p.

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
  | Y => Y
  | V => V
  end.

Notation "x @ f" := (code_sub f x)%code : code_scope.

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

(** ** Abstraction *)

Fixpoint code_abs {Var Var' : Set} (b : Var -> option Var') (x : Code Var) :
  Code Var' :=
  match x with
  | code_var v =>
      match b v with
      | None => I
      | Some v' => K * (code_var v')
      end
  | l * r =>
      match code_abs b l, code_abs b r with
      (* TODO switch to more efficient lambda abstraction once proof passes
      *)
      | K * l', I => l'
      | K * l', K * r' => K * (l' * r')
      | K * l', r' => B * l' * r'
      | l', K * r' => C * l' * r'
      (*
      *)
      | l', r' => S * l' * r'
      end
  | TOP => K * TOP
  | BOT => K * BOT
  | J => K * J
  | R => K * R
  | I => K * I
  | K => K * K
  | B => K * B
  | C => K * C
  | S => K * S
  | Y => K * Y
  | V => K * V
  end.

Section beta_abs_sub.
  Variable Var Var' : Set.
  Variable b : Var -> option Var'.
  Variable x : Code Var.
  Variable y : Code Var'.
  Let f v := match b v with None => y | Some v' => code_var v' end.

  Lemma beta_abs_sub : beta (code_abs b x * y) (code_sub f x).
  Proof.
    induction x; try (unfold f; simpl; auto; fail).
      compute; case (b v); auto.
    (* TODO this only works for simple I,K,S-abstraction.
    compute; rewrite beta_s.
    transitivity (code_abs b c1 * y * (code_sub f c2)); auto.
    *)
  Admitted.
End beta_abs_sub.
Hint Resolve beta_abs_sub.

(** Sloppy lambda notation specialized to [Code nat] *)

Definition open {Var : Set} (x : Code Var) : Code (nat + Var) :=
  code_sub (fun v => code_var (@inr nat Var v)) x.
Definition close {Var : Set} (x : Code (nat + Var)) : Code Var :=
  code_sub (fun v => match v with inr v' => code_var v' | _ => code_top end) x.
Definition make_var (Var : Set) (n : nat) : Code (nat + Var) :=
  code_var (@inl nat Var n).

Definition code_lambda {Var : Set} (x y : Code (nat + Var)) :
  Code (nat + Var) :=
  let beq_var (v1 v2 : nat + Var) : bool :=
    match v1, v2 with
    | inl n1, inl n2 => beq_nat n1 n2
    | _, _ => false
    end
  in
  match x with
  | code_var v => code_abs (fun v' => if beq_var v v' then None else Some v') y
  | _ => BOT (* TODO implement pattern matching here *)
  end.

Notation "\ x , y" := (code_lambda x y)%code : code_scope.

(** ** Information ordering and observable equivalence *)

Definition code_le {Var : Set} (x y : Code Var) :=
  forall (Var' : Set) (c : Code Var') (f : Var -> Code Var'),
  conv (c * (x @ f)) -> conv (c * (y @ f)).
Notation "x [= y" := (code_le x y)%code : code_scope.

Definition code_eq {Var : Set} (x y : Code Var) := x [= y /\ y [= x.
Notation "x == y" := (code_eq x y)%code : code_scope.

Instance code_le_eq_subrelation (Var : Set) :
  subrelation (@code_eq Var) (@code_le Var).
Proof.
  unfold subrelation, predicate_implication, pointwise_lifting.
  unfold code_eq; intros x y [xy yx]; auto.
Qed.

Instance code_le_beta_proper (Var : Set) :
  Proper (beta ==> beta ==> iff) (@code_le Var).
Proof.
  intros x x' Hx y y' Hy; split; unfold code_le; intros Hle Var' c f Hc.
    rewrite <- Hy; apply Hle; rewrite -> Hx; auto.
  rewrite -> Hy; apply Hle; rewrite <- Hx; auto.
Qed.

Instance code_eq_beta_proper (Var : Set) :
  Proper (beta ==> beta ==> iff) (@code_eq Var).
Proof.
  unfold code_eq.
  intros x x' xx' y y' yy'; split; intros [xy yx].
    split; rewrite <- xx'; rewrite <- yy'; auto.
  split; rewrite -> xx'; rewrite -> yy'; auto.
Qed.

Lemma code_le_beta (Var : Set) (x y : Code Var) : beta x y -> x [= y.
Proof.
  unfold code_le; intros H Var' c f Hc.
  rewrite <- H; auto.
Qed.
Hint Resolve code_le_beta.

Instance code_le_beta_subrelation (Var : Set) :
  subrelation beta code_le := code_le_beta Var.

Lemma code_eq_beta (Var : Set) (x y : Code Var) : beta x y -> x == y.
Proof.
  unfold code_le; intro H; split; intros Var' c f Hc.
  rewrite <- H; auto.
  rewrite -> H; auto.
Qed.
Hint Resolve code_eq_beta.

Instance code_eq_beta_subrelation (Var : Set) :
  subrelation beta code_eq := code_eq_beta Var.

Instance code_le_pi_proper (Var : Set) :
  Proper (pi ++> pi --> impl) (@code_le Var).
Proof.
  intros x x' Hx y y' Hy; unfold code_le; intros Hle Var' c f Hc.
  unfold flip in *.
  rewrite (pi_ap_right (code_sub_pi_right _ _ _ _ _ Hy)).
  apply Hle. rewrite -> Hx. auto.
Qed.

Instance code_le_pi_subrelation (Var : Set) :
  subrelation (inverse pi) (@code_le Var).
Proof.
  unfold subrelation, predicate_implication, pointwise_lifting, flip.
  intros x y H; unfold code_le; intros Var' c f Hc.
  rewrite -> H; auto.
Qed.

Instance code_le_refl (Var : Set) : Reflexive (@code_le Var).
Proof. unfold code_le; auto. Qed.

Instance code_eq_refl (Var : Set) : Reflexive (@code_eq Var).
Proof. simpl_relation. Qed.

Instance code_le_trans (Var : Set) : Transitive (@code_le Var).
Proof. unfold code_le; auto. Qed.

Instance code_eq_trans (Var : Set) : Transitive (@code_eq Var).
Proof.
  unfold code_eq, code_le; simpl_relation.
Qed.

Instance code_eq_sym (Var : Set) : Symmetric (@code_eq Var).
Proof.
  unfold code_eq, code_le; simpl_relation.
Qed.

Instance code_le_preorder (Var : Set) : PreOrder (@code_le Var).
Proof.
  split; [apply code_le_refl | apply code_le_trans].
Qed.

Instance code_eq_equivalence (Var : Set) : Equivalence (@code_eq Var).
Proof.
  split; [apply code_eq_refl | apply code_eq_sym | apply code_eq_trans].
Qed.

Instance code_le_partialorder (Var : Set) :
  PartialOrder (@code_eq Var) (@code_le Var).
Proof. simpl_relation. Qed.

Lemma code_le_ap_right (Var : Set) (x y y' : Code Var) :
  y [= y' -> x * y [= x * y'.
Proof.
  unfold code_le, conv; intros H Var' c f.
  repeat rewrite code_sub_ap.
  intros Hconv.
  rewrite <- (beta_ap_right beta_b); apply H.
  rewrite -> (beta_ap_right beta_b); auto.
Qed.
Hint Resolve code_le_ap_right.

Lemma code_le_ap_left (Var : Set) (x x' y : Code Var) :
  x [= x' -> x * y [= x' * y.
Proof.
  unfold code_le, conv; intros H Var' c f.
  repeat rewrite code_sub_ap.
  intros Hconv.
  rewrite <- (beta_ap_right (beta_ap_right (beta_ap_left beta_i))).
  rewrite <- (beta_ap_right (beta_ap_right beta_c)).
  rewrite <- (beta_ap_right beta_b).
  apply H.
  rewrite -> (beta_ap_right beta_b).
  rewrite -> (beta_ap_right (beta_ap_right beta_c)).
  rewrite -> (beta_ap_right (beta_ap_right (beta_ap_left beta_i))).
  auto.
Qed.
Hint Resolve code_le_ap_left.

Lemma code_le_ap (Var : Set) (x x' y y' : Code Var) :
  x [= x' -> y [= y' -> x * y [= x' * y'.
Proof.
  intros Hx Hy; transitivity (x * y'); auto.
Qed.
Hint Resolve code_le_ap.

Lemma code_eq_ap_right (Var : Set) (x y y' : Code Var) :
  y == y' -> x * y == x * y'.
Proof.
  unfold code_eq; intros [H H']; split; auto.
Qed.
Hint Resolve code_eq_ap_right.

Lemma code_eq_ap_left (Var : Set) (x x' y : Code Var) :
  x == x' -> x * y == x' * y.
Proof.
  unfold code_eq; intros [H H']; split; auto.
Qed.
Hint Resolve code_eq_ap_left.

Lemma code_eq_ap (Var : Set) (x x' y y' : Code Var) :
  x == x' -> y == y' -> x * y == x' * y'.
Proof.
  intros Hx Hy; transitivity (x * y'); auto.
Qed.
Hint Resolve code_eq_ap.

Instance code_ap_le (Var : Set) :
  Proper (code_le ==> code_le ==> code_le) (@code_ap Var).
Proof.
  intros x x' Hx y y' Hy.
  apply code_le_trans with (x * y'); auto.
Qed.

Instance code_ap_eq (Var : Set) :
  Proper (code_eq ==> code_eq ==> code_eq) (@code_ap Var).
Proof.
  intros x x' Hx y y' Hy.
  apply code_eq_trans with (x * y'); auto.
Qed.

Ltac code_le_monotonicity := repeat (
  apply code_le_ap_left ||
  apply code_le_ap_right ||
  apply code_le_ap).

Ltac code_eq_monotonicity := repeat (
  apply code_eq_ap_left ||
  apply code_eq_ap_right ||
  apply code_eq_ap).

Ltac monotonicity :=
  match goal with
  | [|- _ [= _] => code_le_monotonicity
  | [|- _ == _] => code_eq_monotonicity
  end.

Instance code_abs_le (Var Var' : Set) (b : Var -> option Var') :
  Proper (code_le ==> code_le) (code_abs b).
Proof.
  intros x x' Hx.
Admitted.

Instance code_abs_eq (Var Var' : Set) (b : Var -> option Var') :
  Proper (code_eq ==> code_eq) (code_abs b).
Proof.
  intros x x' Hx.
Admitted.

Instance code_close_le (Var : Set) : Proper (code_le ==> code_le) (@close Var).
Proof.
  intros x x' xx'.
Admitted.

Instance code_close_eq (Var : Set) : Proper (code_eq ==> code_eq) (@close Var).
Proof.
  intros x x' xx'.
Admitted.

Lemma code_le_top (Var : Set) (x : Code Var) : x [= TOP.
Proof.
  unfold code_le, conv ; intros Var' c f Hred.
  simpl.
  rewrite <- beta_b.
  rewrite -> (pi_top (x @ f)) at 1.
  rewrite -> beta_b; auto.
Qed.
Hint Resolve code_le_top.

Lemma code_le_bot (Var : Set) (x : Code Var) : BOT [= x.
Proof.
  unfold code_le, conv; intros Var' c f Hred.
  rewrite <- beta_b.
  rewrite -> (pi_ap_right (pi_bot _)).
  rewrite -> beta_b; auto.
Qed.
Hint Resolve code_le_bot.

(** *** Proving information ordering *)

Lemma code_le_j_left (Var : Set) (x y : Code Var) : x [= x || y.
Proof.
  unfold code_le, conv; intros Var' c f Hred.
  rewrite pi_j_left; auto.
Qed.
Hint Resolve code_le_j_left.

Lemma code_le_j_right (Var : Set) (x y : Code Var) : y [= x || y.
Proof.
  unfold code_le, conv; intros Var' c f Hred.
  rewrite pi_j_right; auto.
Qed.
Hint Resolve code_le_j_right.

Lemma code_le_j_ub (Var : Set) (x y z : Code Var) :
  x [= z -> y [= z -> x || y [= z.
Proof.
  unfold code_le, conv; intros Hx Hy Var' c f Hconv.
Admitted.
Hint Resolve code_le_j_ub.

Lemma code_le_join (Var : Set) (x y z : Code Var) :
  x || y [= z <-> x [= z /\ y [= z.
Proof.
  split; intro H.
    split; apply code_le_trans with (x || y); auto.
  destruct H as [Hx Hy]; auto.
Qed.
Hint Resolve code_le_join.

Lemma code_le_eq_j (Var : Set) (x y : Code Var) : x [= y <-> y == y || x.
Proof.
  split; intro H; [split | rewrite H]; auto.
Qed.

Lemma code_le_j_idem (Var : Set) (x : Code Var) : x||x [= x.
Proof.
  apply code_le_join; split; reflexivity.
Qed.
Hint Resolve code_le_j_idem.

Lemma code_eq_j_idem (Var : Set) (x : Code Var) : x||x == x.
Proof. split; auto. Qed.
Hint Resolve code_eq_j_idem.

Lemma code_le_j_sym (Var : Set) (x y : Code Var) : x||y == y||x.
Proof. split; auto. Qed.

Lemma code_le_j_assoc (Var : Set) (x y z : Code Var) : x||(y||z) == (x||y)||z.
Proof.
  split; auto.
    apply code_le_j_ub; auto.
    transitivity (x||y); auto.
  apply code_le_j_ub; auto.
  transitivity (y||z); auto.
Qed.

Lemma code_le_j_bot_left (Var : Set) (x : Code Var) : BOT || x == x.
Proof. split; auto. Qed.
Hint Rewrite code_le_j_bot_left : code_simpl.

Lemma code_le_j_bot_right (Var : Set) (x : Code Var) : x || BOT == x.
Proof. split; auto. Qed.
Hint Rewrite code_le_j_bot_right : code_simpl.

Lemma code_le_j_top_left (Var : Set) (x : Code Var) : TOP || x == TOP.
Proof. split; auto. Qed.
Hint Rewrite code_le_j_top_left : code_simpl.

Lemma code_le_j_top_right (Var : Set) (x : Code Var) : x || TOP == TOP.
Proof. split; auto. Qed.
Hint Rewrite code_le_j_top_right : code_simpl.

(** *** Reasoning with extensionality *)

(*
Ltac abstract M x :=
  match m with
  | x => code_ap code_i x
  | code_ap ?M1 ?M2 =>
    let code_ap N1 _ := abstract M1 x in
    let code_ap N2 _ := abstract M2 x in
    code_ap (code_ap (code_ap code_s N1) N2) x
  | _ => code_ap code_k x
  end.

Ltac beta_subs :=
  match goal with
  | beta x y
*)

Lemma code_le_extensionality (Var : Set) (x x' : Code Var) :
  (forall y, x * y [= x' * y) -> x [= x'.
Proof.
  unfold code_le; intros H Var' c f Hconv.
  (* TODO implement via abstraction algorithm *)
Admitted.

Lemma code_eq_extensionality (Var : Set) (x x' : Code Var) :
  (forall y, x * y == x' * y) -> x == x'.
Proof.
  intro H; split; apply code_le_extensionality; apply H.
Qed.

Tactic Notation "eta_expand" :=
  let x := fresh in
  match goal with
  | [|- _ [= _] => apply code_le_extensionality; intro x
  | [|- _ == _] => apply code_eq_extensionality; intro x
  end.

Tactic Notation "eta_expand" "as" ident(x) :=
  match goal with
  | [|- _ [= _] => apply code_le_extensionality; intro x
  | [|- _ == _] => apply code_eq_extensionality; intro x
  end.

Tactic Notation "eta_expand" "in" hyp(H) :=
  eapply code_le_ap_left in H; beta_reduce in H.

Ltac beta_eta :=
  beta_reduce; auto
  || eta_expand; beta_reduce; auto
  || eta_expand; eta_expand; beta_reduce; auto
  || eta_expand; eta_expand; eta_expand; beta_reduce; auto.

Lemma code_eq_ap_top (Var : Set) (x : Code Var) : TOP * x == TOP.
Proof.
  split; auto.
  unfold code_le, conv; intros Var' c f H.
  rewrite (pi_top (K * TOP)); beta_simpl; auto.
Qed.
Hint Rewrite code_eq_ap_top : code_simpl.

Lemma code_eq_ap_bot (Var : Set) (x : Code Var) : BOT * x == BOT.
Proof.
  split; auto.
  unfold code_le, conv; intros Var' c f H.
Admitted.
Hint Rewrite code_eq_ap_bot : code_simpl.

(** *** Closed terms *)

(** A term is closed if it has no variables.
    In proving [x [= y], it will sometimes be easier to consider only
    closing variable assignments [f : Var -> Code Empty_set].
    Thus we introduce an equivalent definition of [x [= y]. *)

Definition code_le_empty {Var : Set} (x y : Code Var) :=
  let Var' := Empty_set in
  forall (c : Code Var') (f : Var -> Code Var'),
  conv (c * (x @ f)) -> conv (c * (y @ f)).

Lemma code_le_empty_complete (Var : Set) (x x' : Code Var) :
  x [= x' -> code_le_empty x x'.
Proof.
  unfold code_le, code_le_empty; intros; auto.
Qed.

Lemma code_le_empty_sound (Var : Set) (x x' : Code Var) :
  code_le_empty x x' -> x [= x'.
Proof.
  unfold code_le; intros H Var' c f Hconv.
Admitted.

Theorem code_le_empty_equiv (Var : Set) (x x' : Code Var) :
  x [= x' <-> code_le_empty x x'.
Proof.
  split; [apply code_le_empty_complete | apply code_le_empty_sound].
Qed.

(** *** A head-normalized definition of convergence *)

Fixpoint code_apply {Var : Set} (x : Code Var) (ys : list (Code Var)) :
  Code Var :=
  match ys with
  | nil => x
  | (y ::ys')%list => code_apply (x * y) ys'
  end.

Notation "x ** y" := (code_apply x y)%code : code_scope.

Fixpoint code_tuple {Var : Set} (ys : list (Code Var)) : Code Var :=
  match ys with
  | nil => I
  | (y :: ys')%list => code_tuple ys' o (C * I * y)
  end.

Lemma beta_tuple_apply (Var : Set) (ys : list (Code Var)) :
  forall x : Code Var, beta (code_tuple ys * x) (x ** ys).
Proof.
  induction ys; simpl; auto; intro x.
  rewrite beta_b.
  rewrite beta_c.
  rewrite beta_i.
  auto.
Qed.
Hint Resolve beta_tuple_apply.

Lemma beta_apply_tuple (Var : Set) (ys : list (Code Var)) :
  forall x : Code Var, beta (x ** ys) (code_tuple ys * x).
Proof.
  induction ys; simpl; auto; intro x.
  rewrite beta_b.
  rewrite beta_c.
  rewrite beta_i.
  auto.
Qed.
Hint Resolve beta_apply_tuple.

Definition code_le_apply {Var : Set} (x x' : Code Var) : Prop :=
  forall (Var' : Set) (ys : list (Code Var')) (f : Var -> Code Var'),
  conv ((x @ f) ** ys) -> conv ((x' @ f) ** ys).

Lemma code_le_apply_complete (Var : Set) (x x' : Code Var) :
  x [= x' -> code_le_apply x x'.
Proof.
  unfold code_le; intros H Var' ys f Hconv.
  rewrite beta_apply_tuple; apply H.
  rewrite beta_tuple_apply; auto.
Qed.

Lemma code_le_apply_sound (Var : Set) (x x' : Code Var) :
  code_le_apply x x' -> x [= x'.
Proof.
  unfold code_le; intros H Var' c f Hconv.
  assert (forall (ys : list (Code Var')),
    conv ((x @ f) ** ys) -> conv ((x' @ f) ** ys)) as H'; auto; clear H.
  set (y := x @ f) in *; set (y' := x' @ f) in *.
  inversion Hconv; simpl; auto.
Admitted.

Theorem code_le_apply_equiv (Var : Set) (x x' : Code Var) :
  x [= x' <-> code_le_apply x x'.
Proof.
  split; [apply code_le_apply_complete | apply code_le_apply_sound].
Qed.
