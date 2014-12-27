(** * This follows the axiomatic treatment of reals
    in the Coq standard library. *)

(** ** Axioms *)

Axiom Ob : Set.

Axiom BOT : Ob.
Axiom TOP : Ob.
Axiom I : Ob.
Axiom K : Ob.
Axiom F : Ob.
Axiom B : Ob.
Axiom C : Ob.
Axiom W : Ob.
Axiom S : Ob.
Axiom R : Ob.
Axiom J : Ob.
Axiom AP : Ob -> Ob -> Ob.
Axiom LESS : Ob -> Ob -> Prop.
Axiom Join : (Ob -> Prop) -> Ob.

Notation "x * y" := (AP x y) (at level 40, left associativity) : Ob_scope.

Open Scope Ob_scope.
Delimit Scope Ob_scope with Ob.
Bind Scope Ob_scope with Ob.

Notation "x 'o' y" := (B * x * y) (at level 30, right associativity) : Ob_scope.
Notation "x || y" := (J * x * y) (at level 50, left associativity) : Ob_scope.
Notation "x (+) y" := (R * x * y) (at level 45, no associativity) : Ob_scope.
Notation "x [= y" := (LESS x y) (at level 60, no associativity) : Ob_scope.

Axiom I_beta: forall x, I*x = x.
Axiom K_beta: forall x y, K*x*y = x.
Axiom F_beta: forall x y, F*x*y = y.
Axiom B_beta: forall x y z, B*x*y*z = x*(y*z).
Axiom C_beta: forall x y z, C*x*y*z = x*z*y.
Axiom W_beta: forall x y, W*x*y = x*y*y.
Axiom S_beta: forall x y z, S*x*y*z = x*z*(y*z).
Axiom J_beta: forall x y z, (x||y)*z = x*z || y*z.
Axiom R_beta: forall x y z, (x(+)y)*z = x*z (+) y*z.
Axiom R_idem: forall x, x(+)x = x.
Axiom R_sym: forall x y, x(+)y = y(+)x.
Axiom R_sym_sym: forall w x y z, (w(+)x) (+) (y(+)z) = (y(+)x) (+) (w(+)z).

Hint Rewrite
  I_beta K_beta F_beta B_beta C_beta
  W_beta S_beta J_beta R_beta R_idem
  : beta.
Ltac beta_reduce := autorewrite with beta.

Axiom LESS_TOP: forall x, x [= TOP.
Axiom LESS_BOT: forall x, BOT [= x.
Axiom J_left: forall x y, x [= x||y.
Axiom J_right: forall x y, y [= x||y.
Axiom J_lub: forall x y z, x [= z -> y [= z -> x||y [= z.
Axiom R_subconvex: forall x y z, x [= z -> y [= z -> x(+)y [= z.
Axiom R_supconvex: forall x y z, z [= x -> z [= x -> z [= x(+)y.
Axiom LESS_refl: forall x, x [= x.
Axiom LESS_antisym: forall x y, x [= y -> y [= x -> x = y.
Axiom LESS_trans: forall x y z, x [= y -> y [= z -> x [= z.
Axiom LESS_AP_left: forall x x' y, x [= x' -> x*y [= x'*y.
Axiom LESS_AP_right: forall x y y', y [= y' -> x*y [= x*y'.

Hint Resolve LESS_TOP.
Hint Resolve LESS_BOT.
Hint Resolve J_left.
Hint Resolve J_right.
Hint Resolve J_lub.
Hint Resolve LESS_refl.
Hint Resolve LESS_antisym.
Hint Resolve LESS_AP_left.
Hint Resolve LESS_AP_right.

Definition is_upper_bound (s : Ob -> Prop) (x : Ob) : Prop :=
  forall y, s y -> y [= x.

Definition is_lub (s : Ob -> Prop) (x : Ob) : Prop :=
  is_upper_bound s x /\ forall y, is_upper_bound s y -> x [= y.

Axiom Join_lub: forall s, is_lub s (Join s).

Lemma J_sym: forall x y, x||y = y||x.
Proof.
  intros x y.
  apply LESS_antisym; auto.
Qed.

Lemma less_eq_join: forall x y, x [= y <-> y = x || y.
Proof.
  intros x y; split; intro H.
  apply LESS_antisym; auto.
  rewrite H; auto.
Qed.

(** ** Global properties *)

Axiom consistency: ~ TOP [= BOT.

Theorem completeness: forall s, exists x, is_lub s x.
Proof.
  intros s.
  exists (Join s).
  apply Join_lub.
Qed.

Axiom extensionality: forall f g, (forall x, f * x = g * x) -> f = g.

Lemma less_extensionality: forall f g, (forall x, f * x [= g * x) -> f [= g.
Proof.
  intros f g H.
  apply less_eq_join.
  apply extensionality; intro x.
  rewrite J_beta; auto.
Qed.

Ltac eta_expand :=
  let x := fresh in
  match goal with
  | [|- _ = _] => apply extensionality; intro x
  | [|- _ [= _] => apply less_extensionality; intro x
  end.

Lemma B_assoc: forall f g h, (f o g) o h = f o (g o h).
Proof.
  intros f g h.
  eta_expand; beta_reduce; auto.
Qed.

Lemma TOP_beta: forall x, TOP*x = TOP.
Proof.
  intro x.
  apply LESS_antisym.
  apply LESS_TOP.
  apply LESS_trans with (K*TOP*x).
  beta_reduce; auto.
  apply LESS_AP_left; auto.
Qed.

Lemma BOT_beta: forall x, BOT*x = BOT.
Proof.
  intro x.
  apply LESS_antisym.
  apply LESS_trans with (K*BOT*x).
  apply LESS_AP_left; auto.
  beta_reduce; auto.
  apply LESS_BOT.
Qed.

Lemma TOP_J_left: forall x, TOP||x = TOP.
Proof.
  intro x.
  symmetry.
  rewrite J_sym.
  apply less_eq_join; auto.
Qed.

Lemma TOP_J_right: forall x, x||TOP = TOP.
Proof.
  intro x.
  rewrite J_sym.
  apply TOP_J_left.
Qed.

Lemma BOT_J_left: forall x, BOT||x = x.
Proof.
  intro x.
  symmetry.
  apply less_eq_join; auto.
Qed.

Lemma BOT_J_right: forall x, x||BOT = x.
Proof.
  intro x.
  rewrite J_sym.
  apply BOT_J_left.
Qed.

Hint Rewrite TOP_beta BOT_beta TOP_J_left TOP_J_right BOT_J_left BOT_J_right
  : beta.

(** ** Definability and accessibility *)

Inductive definable : Ob -> Prop :=
  | S_definable: definable S
  | K_definable: definable K
  | R_definable: definable R
  | J_definable: definable J
  | AP_definable x y: definable x -> definable y -> definable (x*y).

Axiom accessibility: forall x : Ob, x = Join (fun y => y [= x /\ definable y).

(** This is specialized to SKJ, TODO update for SKRJ *)
Inductive conv : Ob -> Prop :=
  | conv_TOP : conv TOP
  | conv_AP_TOP x : conv (x * TOP) -> conv x.

Axiom LESS_conv:
  forall x y, (forall f, definable f -> conv (f*x) -> conv (f*y)) -> x [= y.

Lemma eq_conv:
  forall x y, (forall f, definable f -> conv (f*x) <-> conv (f*y)) -> x = y.
Proof.
  intros x y H.
  apply LESS_antisym; apply LESS_conv; intros f Hdef; firstorder.
Qed.
