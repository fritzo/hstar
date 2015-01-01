(** * This follows the axiomatic treatment of reals
    in the Coq standard library. *)

(* TODO try to replace these with the 5 axioms in ../extensionality.v *)

(** ** Axioms *)

Axiom Ob : Set.

(** printing TOP $\top$ *)
(** printing BOT $\bot$ *)

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
Axiom NLESS : Ob -> Ob -> Prop.
Axiom Join : forall {s : Type}, (s -> Ob) -> Ob.

(** We combine replacement with comprehension as [(m for x : s if p)],
    which is more flexible than comprehension alone [{x : s & p}].
    This will be especially useful for constructing [Join]s.  *)
Notation "( m 'for' x1 : t1 )" :=
  (fun x1 : t1 => m)
  (at level 0, x1 at level 99) : type_scope.
Notation "( m 'for' x1 : t1 'if' t2 )" :=
  (fun x : {x1 : t1 & t2} => match x with existT x1 _ => m end)
  (at level 0, x1 at level 99) : type_scope.
Notation "( m 'for' x1 : t1 'if' t2 'if' t3 )" :=
  (fun x : {x1 : t1 & t2 & t3} => match x with existT2 x1 _ _ => m end)
  (at level 0, x1 at level 99) : type_scope.
Notation "( m 'for' x1 : t1 'for' x2 : t2 )" :=
  (fun x : t1 * t2 => match x with (x1, x2) => m end)
  (at level 0, x1 at level 99, x2 at level 99) : type_scope.
Notation "( m 'for' x1 : t1 'for' x2 : t2 'if' t3 )" :=
  (fun x : sigT (fun x12 : t1 * t2 => let (x1, x2) := x12 in t3) =>
  match x with existT (x1, x2) _ => m end)
  (at level 0, x1 at level 99, x2 at level 99) : type_scope.
Notation "( m 'for' x1 : t1 'for' x2 : t2 'if' t3 )" :=
  (fun x : sigT (fun x12 : t1 * t2 => let (x1, x2) := x12 in t3) =>
  match x with existT (x1, x2) _ => m end)
  (at level 0, x1 at level 99, x2 at level 99) : type_scope.
Notation "( m 'for' x1 : t1 'for' x2 : t2 'if' t3 'if' t4 )" :=
  (fun x : sigT2 (fun x12 : t1 * t2 => let (x1, x2) := x12 in t3)
                 (fun x12 : t1 * t2 => let (x1, x2) := x12 in t4) =>
  match x with existT2 (x1, x2) _ _ => m end)
  (at level 0, x1 at level 99, x2 at level 99) : type_scope.

(** printing * $\ensuremath{\ast}$ *)
(** printing )* $\ensuremath{)\ast}$ *)
(** printing *( $\ensuremath{\ast(}$ *)
(** printing )*( $\ensuremath{)\ast(}$ *)

Notation "x * y" := (AP x y) (at level 40, left associativity) : Ob_scope.

Open Scope Ob_scope.
Delimit Scope Ob_scope with Ob.
Bind Scope Ob_scope with Ob.

(** printing (+) $\ensuremath{\oplus}$ *)
(** printing [= $\ensuremath{\sqsubseteq}$ *)
(** printing [!= $\ensuremath{\not\sqsubseteq}$ *)
(** printing =] $\ensuremath{\sqsupseteq}$ *)

Notation "x 'o' y" := (B * x * y) (at level 30, right associativity) : Ob_scope.
Notation "x || y" := (J * x * y) (at level 50, left associativity) : Ob_scope.
Notation "x (+) y" := (R * x * y) (at level 45, no associativity) : Ob_scope.
Notation "x [= y" := (LESS x y) (at level 60, no associativity) : Ob_scope.
Notation "x [!= y" := (NLESS x y) (at level 60, no associativity) : Ob_scope.
Notation "x =] y" := (LESS y x) (at level 60, no associativity, only parsing)
  : Ob_scope.

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
Axiom Join_beta: forall (s : Type) x y, Join x * y = Join (x i * y for i : s).

Hint Rewrite
  I_beta K_beta F_beta B_beta C_beta
  W_beta S_beta J_beta R_beta R_idem Join_beta
  : beta.

Tactic Notation "beta_reduce" := autorewrite with beta.
Tactic Notation "beta_reduce" "in" hyp(H) := autorewrite with beta in H.

(** To avoid nontermination in [beta_reduce],
    we provide a mechanism to "freeze" terms during reduction. *)
Tactic Notation "freeze" reference(c) "in" tactic(tac) :=
  let v := fresh "v" in
  let H := fresh "Hv" in
  assert (exists v, c=v) as H;
  [ exists c; reflexivity
  | destruct H as [v H]; rewrite H; tac; destruct H].


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
Axiom NLESS_def: forall x y, x [!= y <-> exists f, f * x = TOP /\ f * y = BOT.
(*
Axiom NLESS_def: forall x y, x [!= y <-> (x [= y -> TOP [= BOT).
*)

Hint Resolve LESS_TOP.
Hint Resolve LESS_BOT.
Hint Resolve J_left.
Hint Resolve J_right.
Hint Resolve J_lub.
Hint Resolve LESS_refl.
Hint Resolve LESS_antisym.
Hint Resolve LESS_AP_left.
Hint Resolve LESS_AP_right.

Ltac monotonicity := repeat (apply LESS_AP_left || apply LESS_AP_right).

Definition is_upper_bound {s : Type} (e : s -> Ob) (x : Ob) : Prop :=
  forall i, e i [= x.

Definition is_lub {s : Type} (e : s -> Ob) (x : Ob) : Prop :=
  is_upper_bound e x /\ forall y, is_upper_bound e y -> x [= y.

Axiom Join_lub: forall {s : Type} (e : s -> Ob), is_lub e (Join e).

Lemma Join_ub: forall {s : Type} (e : s -> Ob) i, e i [= Join e.
Proof.
  intros s e i; apply Join_lub.
Qed.

Lemma Join_ub_eq: forall {s : Type} (e : s -> Ob) i x, x = e i -> x [= Join e.
Proof.
  intros s e i x Heq; rewrite Heq; apply Join_lub.
Qed.

Lemma Join_empty: forall e : Empty_set -> Ob, Join e = BOT.
Proof.
  intros e.
  apply LESS_antisym.
    apply Join_lub; unfold is_upper_bound; intro i; elim i.
  auto.
Qed.

Lemma Join_single: forall (x : Ob) (s : Type), s -> Join (x for _ : s) = x.
Proof.
  intros x s y.
  apply LESS_antisym;
  apply Join_lub with (e := fun _ : s => x);
  unfold is_upper_bound;
  auto.
Qed.

Lemma J_sym: forall x y, x||y = y||x.
Proof.
  intros x y.
  apply LESS_antisym; auto.
Qed.

Lemma less_eq_join: forall x y, x [= y <-> x || y = y.
Proof.
  intros x y; split; intro H.
  apply LESS_antisym; auto.
  rewrite <- H; auto.
Qed.

(** ** Global properties *)

Axiom consistency: ~ TOP [= BOT.

Theorem completeness: forall {s : Type} (e : s -> Ob), exists x, is_lub e x.
Proof.
  intros s e.
  exists (Join e).
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

Tactic Notation "eta_expand" :=
  let x := fresh in
  match goal with
  | [|- _ = _] => apply extensionality; intro x
  | [|- _ [= _] => apply less_extensionality; intro x
  end.

Tactic Notation "eta_expand" "as" ident(x) :=
  match goal with
  | [|- _ = _] => apply extensionality; intro x
  | [|- _ [= _] => apply less_extensionality; intro x
  end.

Tactic Notation "eta_expand" "in" hyp(H) :=
  eapply LESS_AP_left in H; beta_reduce in H.

Ltac beta_eta :=
  compute; (
  beta_reduce; auto
  || eta_expand; beta_reduce; auto
  || eta_expand; eta_expand; beta_reduce; auto
  || eta_expand; eta_expand; eta_expand; beta_reduce; auto).

Lemma B_assoc: forall f g h, (f o g) o h = f o (g o h).
Proof.
  intros f g h; beta_eta.
Qed.

Lemma TOP_beta: forall x, TOP*x = TOP.
Proof.
  intro x.
  apply LESS_antisym.
  apply LESS_TOP.
  apply LESS_trans with (K*TOP*x).
  beta_eta.
  apply LESS_AP_left; auto.
Qed.

Lemma BOT_beta: forall x, BOT*x = BOT.
Proof.
  intro x.
  apply LESS_antisym.
  apply LESS_trans with (K*BOT*x).
  apply LESS_AP_left; auto.
  beta_eta.
  apply LESS_BOT.
Qed.

Lemma TOP_J_left: forall x, TOP||x = TOP.
Proof.
  intro x.
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

Lemma J_K_F : J = K || F.
Proof.
  beta_eta.
Qed.

Lemma J_Join: J = Join (if b then K else F for b : bool).
Proof.
  rewrite J_K_F.
  apply LESS_antisym.
    apply J_lub.
      apply Join_ub with (e := (if i then K else F for i : bool)) (i := true).
    apply Join_ub with (e := (if i then K else F for i : bool)) (i := false).
  apply Join_lub; unfold is_upper_bound.
  intro b; case b; auto.
Qed.

(** ** Definability and accessibility *)

(* FIXME should [definable] and [conv] be [Set] or [Prop]? *)

Inductive definable : Ob -> Set :=
  | S_definable: definable S
  | K_definable: definable K
  | R_definable: definable R
  | J_definable: definable J
  | AP_definable x y: definable x -> definable y -> definable (x*y).

Hint Constructors definable.

Axiom accessibility:
  forall x : Ob, x = Join (y for y : Ob if definable y).

(** This is specialized to SKJ, TODO update for SKRJ *)
Inductive conv : Ob -> Set :=
  | conv_TOP : conv TOP
  | conv_AP_TOP x : conv (x * TOP) -> conv x.

Hint Constructors conv.

Axiom LESS_conv:
  forall x y, (forall f, definable f -> conv (f*x) -> conv (f*y)) -> x [= y.

Notation "x <--> y" := ((x -> y) * (y -> x))%type
  (at level 95, no associativity) : type_scope.

Lemma eq_conv:
  forall x y, (forall f, definable f -> conv (f*x) <--> conv (f*y)) -> x = y.
Proof.
  intros x y H.
  apply LESS_antisym; apply LESS_conv; intros f Hdef; firstorder.
Qed.
