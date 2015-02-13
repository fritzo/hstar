Require Export DirectedSets.

(** * Points as quotients of indexed codes.

    This development implements a quotient construction
    using five retraction axioms.

    %\cite{cohen2013pragmatic}% assumes decidable equivalence relation,
    and represents quotients of [T:Type] as (here formalized)

    [{Q:Type & (pi:T->Q) & (repr:Q->T) & (forall q:Q, repr (pi q) = q)}].
*)

Axiom Point : Set -> Set.
Axiom denote : forall {Var : Set}, Codes Var -> Point Var.
Axiom access : forall {Var : Set}, Point Var -> Codes Var.
Axiom denote_access : forall (Var : Set) (p : Point Var), p = denote (access p).
Axiom denote_respect :
  forall (Var : Set) (s s' : Codes Var), codes_eq s s' -> denote s = denote s'.

(* Should we add a variable identifiability axiom:
Axiom access_var : forall {Var : Set} (v : Var),
  let v' := codes_code (code_var v) in
  access (denote v') = v'.
*)

Lemma denote_respect' (Var : Set) (p p' : Point Var) :
    codes_eq (access p) (access p') -> p = p'.
Proof.
  intro H.
  rewrite denote_access.
  rewrite denote_access at 1.
  apply denote_respect.
  auto.
Qed.

Notation "[ x ]" := (denote (codes_code x)%code) : point_scope.

Open Scope point_scope.
Delimit Scope point_scope with point.
Bind Scope point_scope with Point.

Definition definable {Var : Set} (p : Point Var) := {x : Code Var & p = [x]}.

Definition point_le {Var : Set} (p p' : Point Var) :=
  codes_le (access p) (access p').

Notation "x [= y" := (point_le x y)%point : point_scope.

Definition point_ap {Var : Set} (p p' : Point Var) :=
  denote (codes_ap (access p) (access p')).

Definition point_sub {Var Var' : Set} (f : Var -> Point Var') (x : Point Var)
  : Point Var' :=
  denote (codes_sub (fun v => access (f v)) (access x)).

Definition point_abs {Var Var' : Set} (b : Var -> option Var') (x : Point Var)
  : Point Var' :=
  denote (codes_abs b (access x)).

Definition point_lambda {Var : Set} (x y : Point (nat + Var)) :
  Point (nat + Var) :=
  denote (codes_lambda (access x) (access y)).

Definition point_close {Var : Set} (x : Point (nat + Var)) : Point Var :=
  denote (codes_close (access x)).

Definition point_sup {Var : Set} {i : Type} (e : i -> Point Var) : Point Var.
Proof.
  apply denote; apply direct; unfold Precodes.
Admitted.

Notation "'TOP'" := [TOP] : point_scope.
Notation "'BOT'" := [BOT] : point_scope.
Notation "'J'" := [J] : point_scope.
Notation "'R'" := [R] : point_scope.
Notation "'I'" := [I] : point_scope.
Notation "'K'" := [K] : point_scope.
Notation "'B'" := [B] : point_scope.
Notation "'C'" := [C] : point_scope.
Notation "'S'" := [S] : point_scope.
Notation "x * y" := (point_ap x y)%point : point_scope.
Notation "x 'o' y" := (B * x * y)%point : point_scope.
Notation "x || y" := (J * x * y)%point : point_scope.
Notation "x (+) y" := (R * x * y)%point : point_scope.
Notation "x @ f" := (point_sub f x)%point : point_scope.
Notation "\ x , y" := (point_lambda x y)%point : point_scope.

Definition point_nle {Var : Set} (x y : Point Var) : Prop :=
  exists Var' : Set,
  exists c : Point Var',
  exists f : Var -> Point Var',
  c * (x @ f) = TOP /\ c * (y @ f) = BOT.
Notation "x [!= y" := (point_nle x y)%point : point_scope.

Lemma point_ap_respect (Var : Set) (x y : Code Var) : [x * y]%code = [x] * [y].
Proof.
  unfold point_ap, codes_ap.
  (* TODO *)
Admitted.

Lemma point_sub_respect (Var Var' : Set) (f : Var -> Code Var') (x : Code Var)
  : [x] @ (fun v => [f v]%code) = [x @ f]%code.
Proof.
  unfold point_sub, codes_sub.
  (* TODO *)
Admitted.

(** ** Local properties of points *)

Section point_beta.
  Variable Var : Set.
  Variable w x y z : Point Var.

  Lemma point_i_beta : I * x = x.
  Admitted.

  Lemma point_k_beta : K * x * y = x.
  Admitted.

  Lemma point_b_beta : B * x * y * z = x * (y * z).
  Admitted.

  Lemma point_c_beta : C * x * y * z = x * z * y.
  Admitted.

  Lemma point_s_beta : S * x * y * z = x * z * (y * z).
  Admitted.

  Lemma point_j_beta : (x || y) * z = x * z || y * z.
  Admitted.

  Lemma point_r_beta : (x (+) y) * z = x * z (+) y * z.
  Admitted.

  Lemma point_r_idem : x (+) x = x.
  Admitted.

  Lemma point_r_sym : x (+) y = y (+) x.
  Admitted.

  Lemma point_r_sym_sym : (w(+)x) (+) (y(+)z) = (y(+)x) (+) (w(+)z).
  Admitted.

  Variable index : Type.
  Variable e : index -> Point Var.

  Lemma point_sup_beta : point_sup e * y = point_sup (e i * y for i : index).
  Admitted.
End point_beta.

Hint Rewrite
  point_i_beta point_k_beta point_b_beta point_c_beta
  point_s_beta point_j_beta point_r_beta point_r_idem point_sup_beta
  : beta.

Tactic Notation "beta_reduce" :=
  repeat rewrite point_ap_respect;
  autorewrite with beta.
Tactic Notation "beta_reduce" "in" hyp(H) :=
  repeat rewrite point_ap_respect in H;
  autorewrite with beta;
  autorewrite with beta in H.

Section point_algebra.
  Variable Var : Set.
  Variable x x' y y' z : Point Var.

  Lemma point_le_top : x [= TOP.
  Admitted.

  Lemma point_le_bot : BOT [= x.
  Admitted.

  Lemma point_j_left : x [= x || y.
  Admitted.

  Lemma point_j_right : y [= x || y.
  Admitted.

  Lemma point_j_lub : x [= z -> y [= z -> x || y [= z.
  Admitted.

  Lemma point_r_subconvex : x [= z -> y [= z -> x(+)y [= z.
  Admitted.

  Lemma point_r_supconvex : z [= x -> z [= x -> z [= x(+)y.
  Admitted.

  Lemma point_le_refl : x [= x.
  Admitted.

  Lemma point_le_antisym : x [= y -> y [= x -> x = y.
  Admitted.

  Lemma point_le_trans : x [= y -> y [= z -> x [= z.
  Admitted.

  Lemma point_le_ap_left : x [= x' -> x * y [= x' * y.
  Admitted.

  Lemma point_le_ap_right : y [= y' -> x * y [= x * y'.
  Admitted.

  Lemma point_le_ap : x [= x' -> y [= y' -> x * y [= x' * y'.
  Admitted.
End point_algebra.

Hint Resolve point_le_top.
Hint Resolve point_le_bot.
Hint Resolve point_j_left.
Hint Resolve point_j_right.
Hint Resolve point_j_lub.
Hint Resolve point_le_refl.
Hint Resolve point_le_antisym.
Hint Resolve point_le_ap_left.
Hint Resolve point_le_ap_right.
Hint Resolve point_le_ap.

Ltac monotonicity := repeat (
  apply point_le_ap_left ||
  apply point_le_ap_right ||
  apply point_le_ap).

(** Properties of [sup] *)

Section point_join.
  Variable Var : Set.
  Variable x y z : Point Var.

  Lemma point_join_sym : x || y = y || x.
  Proof.
    auto.
  Qed.

  Lemma point_le_eq_join : x [= y <-> x || y = y.
  Proof.
    split; intro H.
    apply point_le_antisym; auto.
    rewrite <- H; auto.
  Qed.
End point_join.

Definition is_upper_bound {Var : Set} {s : Type}
  (e : s -> Point Var) (x : Point Var) : Prop :=
  forall i, e i [= x.

Definition is_lub {Var : Set} {s : Type}
  (e : s -> Point Var) (x : Point Var) : Prop :=
  is_upper_bound e x /\ forall y, is_upper_bound e y -> x [= y.

Section point_sup_lub.
  Variable Var : Set.
  Variable index : Type.
  Variable e : index -> Point Var.

  Lemma point_sup_lub : is_lub e (point_sup e).
  Admitted.

  Lemma point_sup_ub : forall i, e i [= point_sup e.
  Proof.
    apply point_sup_lub.
  Qed.

  Lemma point_sup_ub_eq : forall i x, x = e i -> x [= point_sup e.
  Proof.
    intros i x Heq; rewrite Heq; apply point_sup_lub.
  Qed.
End point_sup_lub.

Section point_sup_empty.
  Variable Var : Set.

  Lemma point_sup_empty (e : Empty_set -> Point Var) : point_sup e = BOT.
  Proof.
    apply point_le_antisym.
      apply point_sup_lub; unfold is_upper_bound; intro i; elim i.
    auto.
  Qed.

  Lemma point_sup_single (x : Point Var) (s : Type) :
    s -> point_sup (x for _ : s) = x.
  Proof.
    intros y.
    apply point_le_antisym;
    apply point_sup_lub with (e := fun _ : s => x);
    unfold is_upper_bound;
    auto.
  Qed.
End point_sup_empty.

(** ** Global properties of [Points] *)

Theorem consistency (Var : Set) : [@code_top Var] <> [@code_bot Var].
Proof.
  (* TODO apply access_denote. *)
Admitted.

Theorem completeness (Var : Set) (s : Type) (e : s -> Point Var) :
  exists x, is_lub e x.
Proof.
  exists (point_sup e); apply point_sup_lub.
Qed.

Theorem extensionality (Var : Set) (f g : Point Var) :
  (forall x, f * x = g * x) -> f = g.
Proof.
  (* TODO *)
Admitted.

Corollary point_le_extensionality (Var : Set) (f g : Point Var) :
  (forall x, f * x [= g * x) -> f [= g.
Proof.
  intros H.
  apply point_le_eq_join.
  apply extensionality; intro x.
  rewrite point_j_beta; auto.
Qed.

(** ** Example reasoning using beta-eta conversion *)

Tactic Notation "eta_expand" :=
  let x := fresh in
  match goal with
  | [|- _ = _] => apply extensionality; intro x
  | [|- _ [= _] => apply point_le_extensionality; intro x
  end.

Tactic Notation "eta_expand" "as" ident(x) :=
  match goal with
  | [|- _ = _] => apply extensionality; intro x
  | [|- _ [= _] => apply point_le_extensionality; intro x
  end.

Tactic Notation "eta_expand" "in" hyp(H) :=
  eapply point_le_ap_left in H; beta_reduce in H.

Ltac beta_eta :=
  simpl; (
  beta_reduce; auto
  || eta_expand; beta_reduce; auto
  || eta_expand; eta_expand; beta_reduce; auto
  || eta_expand; eta_expand; eta_expand; beta_reduce; auto).

Section point_b_assoc.
  Variable Var : Set.
  Variable x y z : Point Var.

  Lemma point_b_assoc : (x o y) o z = x o (y o z).
  Proof.
    beta_eta.
  Qed.

  Lemma point_beta_top : TOP * x = TOP.
  Proof.
    apply point_le_antisym.
    apply point_le_top.
    apply point_le_trans with (K * TOP * x).
    beta_eta.
    apply point_le_ap_left; auto.
  Qed.

  Lemma point_beta_bot : BOT * x = BOT.
  Proof.
    apply point_le_antisym.
    apply point_le_trans with (K*BOT*x).
    apply point_le_ap_left; auto.
    beta_eta.
    apply point_le_bot.
  Qed.

  Lemma point_beta_join_top_left : TOP || x = TOP.
  Proof.
    rewrite point_join_sym; apply point_le_eq_join; auto.
  Qed.

  Lemma point_beta_join_top_right : x || TOP = TOP.
  Proof.
    rewrite point_join_sym; apply point_beta_join_top_left.
  Qed.

  Lemma point_beta_join_bot_left : BOT || x = x.
  Proof.
    apply point_le_eq_join; auto.
  Qed.

  Lemma point_beta_join_bot_right : x || BOT = x.
  Proof.
    rewrite point_join_sym; apply point_beta_join_bot_left.
  Qed.
End point_b_assoc.

Hint Rewrite
  point_beta_top point_beta_bot
  point_beta_join_top_left point_beta_join_top_right
  point_beta_join_bot_left point_beta_join_bot_right
  : beta.

Lemma point_j_k_ki (Var : Set) : (J : Point Var) = K || K*I.
Proof.
  beta_eta.
Qed.

Section point_sup_pair.
  Variable Var : Set.
  Let bool_to_point (b : bool) : Point Var := if b then K else K * I.
  Lemma point_sup_pair : J = point_sup bool_to_point.
  Proof.
    rewrite point_j_k_ki.
    apply point_le_antisym.
      apply point_j_lub.
        apply point_sup_ub with (e := bool_to_point) (i := true).
      apply point_sup_ub with (e := bool_to_point) (i := false).
    apply point_sup_lub; unfold is_upper_bound.
    intro b; case b; auto.
  Qed.
End point_sup_pair.
