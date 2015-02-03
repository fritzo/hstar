Require Import Coq.Logic.Classical_Prop.
Require Import Coq.Classes.Morphisms.
Require Export TypeConstructor.
Require Import Nontermination.
Require Import LeastFixedPoint.
Require Import BohmTrees.
Open Scope code_scope.

(** * Types as closures *)

(** We follow Dana Scott's types-as-closures idiom from \cite{scott1976data}.
    *)

(** ** Properties of types *)

Notation "x :: a" := (a * x == x) : code_scope.

Definition closure {Var : Set} (a : Code Var) := I [= a /\ a o a == a.

Instance closure_proper_eq (Var : Set) :
  Proper (code_eq ==> iff) (@closure Var).
Proof.
  simpl_relation; unfold closure; split; intros [Hn Hi]; split;
  (rewrite -> H || rewrite <- H); auto.
Qed.

Lemma nondecreasing_idempotent (Var : Set) (a : Code Var) :
 I [= a -> a o a [= a -> a o a == a.
Proof.
  intros Hi Hr; split; auto.
  rewrite <- Hi at 2; beta_eta.
Qed.
Hint Resolve nondecreasing_idempotent.

Lemma closure_weak (Var : Set) (a : Code Var) :
 I [= a -> a o a [= a -> closure a.
Proof.
  unfold closure; intros; split; auto.
Qed.

(* ------------------------------------------------------------------------ *)
(** ** [V] is the type of all types *)

Lemma V1_nondecreasing (Var : Set) (a : Code Var) : I [= V * a.
Proof.
  simpl; unfold V; fold (@Y Var).
  eta_expand as x; code_simpl; rewrite code_eq_y; code_simpl; auto.
Qed.

Lemma V1_idempotent (Var : Set) (a : Code Var) : (V * a) o (V * a) == (V * a).
Proof.
  split.
    unfold V; fold (@Y Var).
    eta_expand; beta_simpl.
    admit. (* TODO *)
  apply V_as_limit; intro n; induction n; simpl.
    rewrite <- (V1_nondecreasing _ a); beta_eta.
  rewrite IHn.
  rewrite code_eq_v at 3.
  rewrite pi_j_right.
  eta_expand; beta_simpl; auto.
Qed.
Hint Rewrite V1_idempotent : code_simpl.

Lemma V_nondecreasing (Var : Set) : I [= (V : Code Var).
Proof.
  eta_expand.
  rewrite code_eq_v; rewrite pi_j_right.
  rewrite code_eq_v; rewrite pi_j_left.
  beta_eta.
Qed.
Hint Resolve V_nondecreasing.

Lemma V_idempotent (Var : Set) : V o V == (V : Code Var).
Proof.
  apply nondecreasing_idempotent; auto.
  eta_expand as a; rewrite beta_b.
  apply V_as_limit; intro n; induction n; simpl.
    unfold V; fold (@Y Var).
    eta_expand as x; code_simpl; rewrite code_eq_y; code_simpl; auto.
   rewrite IHn.
   apply V1_idempotent.
Qed.
Hint Rewrite V_idempotent : code_simpl.

Lemma V_closure (Var : Set) : closure (V : Code Var).
Proof.
  split; [apply V_nondecreasing | apply V_idempotent].
Qed.

Inductive V_fixes {Var : Set} : Code Var -> Prop :=
  V_fixes_intro (x : Code Var) : closure x -> V_fixes x.
Hint Constructors V_fixes.

Instance V_fixes_proper (Var : Set) : Proper (code_eq ==> iff) (@V_fixes Var).
Proof.
  intros x x' xx'; split; intro Hc; inversion Hc; apply V_fixes_intro;
  [rewrite <- xx' | rewrite xx']; auto.
Qed.

Lemma V_sound (Var : Set) (x : Code Var) : x :: V -> V_fixes x.
Proof.
  intros Hfix; apply V_fixes_intro.
  assert (I [= x).
    rewrite <- Hfix; rewrite code_eq_v; auto.
  split; auto.
  rewrite <- Hfix at 3; rewrite code_eq_v; rewrite Hfix.
  split; auto.
  apply code_le_j_ub; auto.
  rewrite <- H; beta_eta.
Qed.

Lemma V_complete (Var : Set) (x : Code Var) : V_fixes x -> x :: V.
Proof.
  intros [a [Hn Hi]].
  split.
    unfold V; fold (@Y Var); beta_simpl.
    apply Y_lfp; beta_simpl.
    apply code_le_join; split; [auto | rewrite Hi; auto].
  rewrite <- V_nondecreasing; beta_eta.
Qed.

Corollary V_fixes_closure (Var : Set) (a : Code Var) : closure a -> a :: V.
Proof.
  intro H; apply V_complete; apply V_fixes_intro; auto.
Qed.

Theorem V_inhab (Var : Set) (x : Code Var) : x :: V <-> V_fixes x.
Proof.
  split; [apply V_sound | apply V_complete].
Qed.

Lemma V_V (Var : Set) : V :: (V : Code Var).
Proof.
  apply V_inhab; apply V_fixes_intro; apply V_closure.
Qed.
Hint Rewrite V_V : code_simpl.

(* ------------------------------------------------------------------------ *)
(** Next some lemmas about inhabinants of V. *)

Lemma V_V1 (Var : Set) (a : Code Var) : V * (V * a) == V * a.
Proof.
  apply V_fixes_closure; split; [apply V1_nondecreasing | apply V1_idempotent].
Qed.
Hint Rewrite V_V1 : code_simpl.

Lemma V1_inhab (Var : Set) (a x : Code Var) : a * x [= x <-> x :: V * a.
Proof.
  split.
    intro H; split.
      apply V1_as_limit; unfold limit_le_code.
      intro n; induction n; simpl; auto.
      beta_simpl; rewrite IHn; auto.
    rewrite <- V1_nondecreasing; beta_simpl; auto.
  intro Hf.
  rewrite <- Hf at 2; rewrite <- V_nondecreasing; beta_eta.
Qed.

Lemma V1_inhab_top (Var : Set) (a : Code Var) : TOP :: V * a.
Proof.
  split; auto; rewrite <- V1_nondecreasing; code_simpl; auto.
Qed.
Hint Rewrite V1_inhab_top : code_simpl.

(* ------------------------------------------------------------------------ *)
(** ** [I] is the largest type, the type of everyting *)

Lemma I_nondecreasing (Var : Set) : I [= (I : Code Var).
Proof.
  auto.
Qed.

Lemma I_idempotent (Var : Set) : I o I == (I : Code Var).
Proof.
  beta_eta.
Qed.
Hint Rewrite I_idempotent : code_simpl.

Lemma V_I (Var : Set) : I :: (V : Code Var).
Proof.
  apply V_fixes_closure;
  split; [apply I_nondecreasing | apply I_idempotent].
Qed.
Hint Rewrite V_I : code_simpl.

Inductive I_fixes {Var : Set} : Code Var -> Prop :=
  I_fixes_intro x : I_fixes x.
Hint Constructors I_fixes.

Instance I_fixes_proper (Var : Set) : Proper (code_eq ==> iff) (@I_fixes Var).
Proof.
  simpl_relation; auto.
Qed.

Theorem I_inhab (Var : Set) (x : Code Var) : x :: I <-> I_fixes x.
Proof.
  beta_reduce; firstorder.
Qed.

(* ------------------------------------------------------------------------ *)
(** ** [P] is a powertype operator *)

(** [P] acts as both a unary subtype operation
    and a binary type intersection operation.
    We start with the unary version. *)

Section P.
  Context {Var : Set}.
  Let a := make_var Var 0.
  Let a' := make_var Var 1.
  Definition P := Eval compute in close_var (\a, \a', V * (a || a')).
End P.

Lemma P_idem (Var : Set) (a : Code Var) : P * a * a == V * a.
Proof.
  unfold P; fold (@V Var); beta_simpl; rewrite code_eq_j_idem; auto.
Qed.
Hint Rewrite P_idem : code_simpl.

Lemma P_comm (Var : Set) (a b : Code Var) : P * a * b == P * b * a.
Proof.
  unfold P; fold (@V Var); beta_simpl; rewrite code_le_j_sym at 1; auto.
Qed.

Lemma code_le_v_join (Var : Set ) (a b : Code Var) :
  V * a || V * b [= V * (a || b).
Proof.
  apply code_le_j_ub; auto.
Qed.

Lemma code_eq_v_join (Var : Set ) (a b : Code Var) :
  V * (V * a || V * b) == V * (a || b).
Proof.
  split.
    rewrite code_le_v_join; code_simpl; auto.
  rewrite <- (beta_left (beta_right beta_i)).
  rewrite <- (beta_right (beta_right beta_i)).
  monotonicity.
Qed.

Lemma code_eq_v_idem (Var : Set ) (a : Code Var) : V * (V * a) == V * a.
Proof.
  rewrite <- beta_b; rewrite V_idempotent; auto.
Qed.
Hint Rewrite code_eq_v_join : code_simpl.

Lemma code_eq_v_join_left (Var : Set ) (a b : Code Var) :
  V * (V * a || b) == V * (a || b).
Proof.
  rewrite <- code_eq_v_join; rewrite code_eq_v_idem.
  rewrite <- (code_eq_v_join _ a b); reflexivity.
Qed.
Hint Rewrite code_eq_v_join_left : code_simpl.

Lemma code_eq_v_join_right (Var : Set ) (a b : Code Var) :
  V * (a || V * b) == V * (a || b).
Proof.
  rewrite <- code_eq_v_join; rewrite code_eq_v_idem.
  rewrite <- (code_eq_v_join _ a b); reflexivity.
Qed.
Hint Rewrite code_eq_v_join_right : code_simpl.

Lemma P_assoc (Var : Set) (a b c : Code Var) :
  P * a * (P * b * c) == P * (P * a * b) * c.
Proof.
  unfold P; fold (@V Var); code_simpl.
  rewrite code_eq_j_assoc; reflexivity.
Qed.

Lemma P1_nondecreasing (Var : Set) (a : Code Var) : I [= P * a.
Proof.
  unfold P; fold (@V Var).
  eta_expand; rewrite beta_b; rewrite beta_b; rewrite pi_j_right.
  monotonicity.
Qed.

Lemma P1_idempotent (Var : Set) (a : Code Var) : (P * a) o (P * a) == P * a.
Proof.
  apply nondecreasing_idempotent.
    apply P1_nondecreasing.
  eta_expand as b; rewrite beta_b.
Admitted.
Hint Rewrite P1_idempotent : code_simpl.

Lemma V_P1 (Var : Set) (a : Code Var) : V * (P * a) == P * a.
Proof.
  apply V_fixes_closure;
  split; [apply P1_nondecreasing | apply P1_idempotent].
Qed.
Hint Rewrite V_P1 : code_simpl.

Inductive P1_fixes {Var : Set} (a : Code Var) : Code Var -> Prop :=
  P1_fixes_intro a' : V_fixes a' -> a [= a' -> P1_fixes a a'.

Instance P1_fixes_proper (Var : Set) :
  Proper (code_eq ==> code_eq ==> iff) (@P1_fixes Var).
Proof.
  intros a a' aa' x x' xx'; split; intro Ha.
    destruct Ha as [x Hv Hl]; apply P1_fixes_intro;
    rewrite <- xx'; try rewrite <- aa'; auto.
  destruct Ha as [x' Hv Hl]; apply P1_fixes_intro;
  rewrite xx'; try rewrite aa'; auto.
Qed.

Lemma P1_sound (Var : Set) (a x : Code Var) : x :: P * a -> P1_fixes a x.
Proof.
  unfold  closure, P; fold (@V Var); beta_simpl.
  intros Hfix.
  assert (I [= x).
    rewrite <- Hfix; rewrite code_eq_v; auto.
  assert (a [= x) as ax.
    rewrite <- Hfix; rewrite <- V_nondecreasing; beta_simpl; auto.
  rewrite code_le_j_sym in Hfix.
  rewrite <- (proj1 (code_le_eq_j Var a x)) in Hfix; auto.
  split; auto.
    apply V_sound; auto.
Qed.

Lemma P1_complete (Var : Set) (a x : Code Var) : P1_fixes a x -> x :: P * a.
Proof.
  unfold  closure; intros [b Hf Hl]; split.
  - rewrite Hl.
    unfold P; fold (@V Var); beta_simpl.
    rewrite code_le_j_idem.
    apply V_complete in Hf; rewrite Hf; auto.
  - assert (b == I * b) as eq; beta_simpl; auto; rewrite eq at 1.
    monotonicity.
    apply (P1_nondecreasing _ a).
Qed.

Theorem P1_inhab (Var : Set) (a x : Code Var) : x :: P * a <-> P1_fixes a x.
Proof.
  split; [apply P1_sound | apply P1_complete].
Qed.

(* ------------------------------------------------------------------------ *)
(** Next we treat [P] as a binary type intersection operation. *)

Lemma P2_nondecreasing (Var : Set) (a b : Code Var) : I [= P * a * b.
Proof.
  unfold P; fold (@V Var); beta_simpl; apply V1_nondecreasing.
Qed.

Lemma P2_idempotent (Var : Set) (a b : Code Var) :
  (P * a * b) o (P * a * b) == P * a * b.
Proof.
  unfold P; fold (@V Var); beta_simpl; apply V1_idempotent.
Qed.
Hint Rewrite P1_idempotent : code_simpl.

Lemma V_P2 (Var : Set) (a b : Code Var) : V * (P * a * b) == P * a * b.
Proof.
  apply V_fixes_closure;
  split; [apply P2_nondecreasing | apply P2_idempotent].
Qed.
Hint Rewrite V_P2 : code_simpl.

Inductive P2_fixes {Var : Set} (a b : Code Var) : Code Var -> Prop :=
  P2_fixes_intro x : x :: V * a -> x :: V * b -> P2_fixes a b x.
  (* Which of these forms is most convenient?
  P2_fixes_intro x : a * x [= x -> b * x [= x -> P2_fixes a b x.
  P2_fixes_intro x : V1_fixes a x -> V1_fixes b x -> P2_fixes a b x.
  *)

Instance P2_fixes_proper (Var : Set) :
  Proper (code_eq ==> code_eq ==> code_eq ==> iff) (@P2_fixes Var).
Proof.
  intros a a' aa' b b' bb' x x' xx'; split; intro Ha; inversion Ha.
  - apply P2_fixes_intro.
    + rewrite <- aa'; rewrite <- xx'; auto.
    + rewrite <- bb'; rewrite <- xx'; auto.
  - apply P2_fixes_intro.
    + rewrite aa'; rewrite xx'; auto.
    + rewrite bb'; rewrite xx'; auto.
Qed.

Lemma P2_sound (Var : Set) (a b x : Code Var) :
  x :: P * a * b -> P2_fixes a b x.
Proof.
  unfold P; fold (@V Var); code_simpl.
  intro Hab; apply V1_inhab in Hab.
  code_simpl in Hab; apply code_le_join in Hab; destruct Hab as [Ha Hb].
  apply P2_fixes_intro; apply V1_inhab; auto.
Qed.

Lemma P2_complete (Var : Set) (a b x : Code Var) :
  P2_fixes a b x -> x :: P * a * b.
Proof.
  intro H; destruct H as [x Ha Hb].
  unfold P; fold (@V Var); code_simpl.
  rewrite <- V1_inhab in Ha.
  rewrite <- V1_inhab in Hb.
  apply V1_inhab; code_simpl; auto.
Qed.

Theorem P2_inhab (Var : Set) (a b x : Code Var) :
  x :: P * a * b <-> P2_fixes a b x.
Proof.
  split; [apply P2_sound | apply P2_complete].
Qed.

Lemma P2_inhab_le (Var : Set) (a b x : Code Var) :
  (a * x [= x /\ b * x [= x) <-> x :: P * a * b.
Proof.
  split.
    intros [Ha Hb].
    unfold P; fold (@V Var); beta_simpl.
    apply V1_inhab; beta_simpl; auto.
  intro Hab.
  unfold P in Hab; fold (@V Var) in Hab; beta_simpl in Hab.
  apply V1_inhab in Hab; beta_simpl in Hab.
  apply code_le_join in Hab; destruct Hab as [Ha Hb].
  split; auto.
Qed.

Lemma P2_fixes_simpl (Var : Set) (a b x : Code Var) :
  (x :: V * a /\ x :: V * b) <-> x :: P * a * b.
Proof.
  rewrite <- P2_inhab_le; repeat rewrite V1_inhab; tauto.
Qed.

(* ------------------------------------------------------------------------ *)
(** ** Closures constructed as [A * f] *)

(* EXPERIMENTAL *)

Inductive type_body {Var : Set} : nat -> nat -> Code (nat + Var) -> Set :=
  | type_body_eq n n' x y : x == y -> type_body n n' x -> type_body n n' y
  | type_body_atom n n' v : v :: V -> type_body n n' v
  | type_body_var n n' : type_body n n' (code_var (inl n'))
  | type_body_exp n n' a b :
      type_body n' n a -> type_body n n' b -> type_body n n' (exp * a * b)
  (*
  | type_body_fix n n' f :
      (forall x, type_body n n' x -> type_body n n' (f * x)) ->
      type_body n n' (Y * f)
  *)
.

Lemma V_fixes_constructed_types
  (Var : Set) (n n' : nat) (f : Code (nat + Var)) :
  type_body n n' f -> (\\code_var (inl n), code_var (inl n'); f) :: V.
Proof.
  intro H; induction H.
  - simpl; rewrite <- c; auto.
  - admit.
  - admit.
  - admit.
Qed.

(* ------------------------------------------------------------------------ *)
(** ** [div] is inhabited by [{BOT, TOP}] *)

Lemma div_nondecreasing (Var : Set) : I [= (div : Code Var).
Proof.
  unfold div; apply V1_nondecreasing.
Qed.

Lemma div_idempotent (Var : Set) : div o div == (div : Code Var).
Proof.
  unfold div; apply V1_idempotent.
Qed.
Hint Rewrite div_idempotent : code_simpl.

Lemma V_div (Var : Set) : V * div == (div : Code Var).
Proof.
  apply V_fixes_closure;
  split; [apply div_nondecreasing | apply div_idempotent].
Qed.
Hint Rewrite V_div : code_simpl.

Lemma div_inhab_bot (Var : Set) : BOT :: (div : Code Var).
Proof.
  apply div_bot.
Qed.
Hint Rewrite div_inhab_bot : code_simpl.

Lemma div_inhab_top (Var : Set) : TOP :: (div : Code Var).
Proof.
  rewrite <- V_div; apply V1_inhab_top.
Qed.
Hint Rewrite div_inhab_top : code_simpl.

Inductive div_fixes {Var : Set} : Code Var -> Prop :=
  | div_fixes_eq x y : x == y -> div_fixes x -> div_fixes y
  | div_fixes_bot : div_fixes BOT
  | div_fixes_top : div_fixes TOP.
Hint Constructors div_fixes.

Instance div_fixes_proper (Var : Set) :
  Proper (code_eq ==> iff) (@div_fixes Var).
Proof.
  intros x y xy; split; [idtac | apply symmetry in xy];
  intro H; induction H; eauto.
Qed.

Theorem div_sound (Var : Set) (x : Code Var) :
  x :: div -> div_fixes x.
Proof.
  intros H.
  case_le (x [= BOT) as H'.
  - assert (x == BOT) as eq. split; auto. rewrite eq; auto.
  - rewrite <- H; clear H.
    rewrite <- conv_nle_bot in H'. (* FIXME *)
    apply conv_div_top in H'; rewrite H'; auto.
Qed.

Theorem div_inhab (Var : Set) (x : Code Var) : x :: div <-> div_fixes x.
Proof.
  split.
    apply div_sound.
  intro H; induction H; code_simpl; auto.
  rewrite <- H; auto.
Qed.

(* We also have an algebraic definition of [div] as nil. *)

Section div'.
  Context {Var : Set}.
  Let a := make_var Var 0.
  Let a' := make_var Var 1.
  Definition div' := Eval compute in close_var (\\a,a'; a').
End div'.

Lemma div'_div (Var : Set) : (div' : Code Var) = div' o div.
Proof.
Admitted.

Lemma div_algebraic (Var : Set) : div' == (div : Code Var).
  rewrite div'_div; eta_expand as x; beta_simpl.
  set (y := div * x); subst; assert (y = div * x) as eq; auto.
  assert (y :: div) as Hf.
    rewrite eq; rewrite <- beta_b; rewrite div_idempotent; auto.
  apply div_inhab in Hf; induction Hf.
  - admit. (* TODO *)
  - unfold div'; code_simpl. admit. (* TODO: case BOT *)
  - unfold div'; code_simpl. admit. (* TODO: case TOP *)
Admitted.

(* this is an ugly proof. why not show [div' : div --> I] then [case_le]? *)
Lemma div_algebraic' (Var : Set) : div' == (div : Code Var).
Proof.
  split.
  - eta_expand as x.
    case_le (x [= BOT).
    + assert (x == BOT) as eq; try (split; auto).
      rewrite eq; clear x eq H.
      unfold div'; fold (@Y Var); code_simpl.
      admit. (* TODO lfp argument *)
    + rewrite <- conv_nle_bot in H.
      apply conv_div_top in H; rewrite H; auto.
  - unfold div, div'; fold (@Y Var).
    rewrite pi_j_left at 1.
    rewrite pi_j_left at 1.
    rewrite pi_j_right at 1.
    beta_simpl.
    (* FIXME it looks like A may need to use Y instead of V *)
Admitted.

(* ------------------------------------------------------------------------ *)
(** ** [semi] represents Sierpinsky space, inhabited by [{BOT, I, TOP}] *)

Section semi.
  Context {Var : Set}.
  Let a := make_var Var 0.
  Let a' := make_var Var 1.
  Definition semi := Eval compute in close_var (\\a,a'; a --> a').
End semi.

Lemma A_exp_semi (Var : Set) : A * exp == (semi : Code Var).
Proof.
  unfold A, exp, semi; beta_simpl; auto.
Qed.

Lemma semi_nondecreasing (Var : Set) : I [= (semi : Code Var).
Proof.
  unfold semi.
  eta_expand.
  rewrite code_eq_y.
  rewrite beta_j_ap.
  rewrite beta_k.
  repeat rewrite pi_j_left.
  beta_eta.
Qed.

Lemma semi_idempotent (Var : Set) : semi o semi == (semi : Code Var).
Proof.
  rewrite <- A_exp_semi.
  split.
  - rewrite A_simpl at 3; rewrite code_eq_y; rewrite <- A_simpl.
    unfold A_step; code_simpl.
    rewrite pi_j_right; rewrite pi_j_left.
    (* TODO argue pairwise <<s o s', r' o r>> *)
    admit.
  - rewrite A_simpl at 2; rewrite code_eq_y; rewrite <- A_simpl.
    unfold A_step; code_simpl.
    rewrite pi_j_left; rewrite pi_j_left; rewrite pi_j_left.
    unfold exp at 2; unfold pair.
    beta_eta.
Qed.
Hint Rewrite semi_idempotent : code_simpl.

(* TODO prove by [apply V_fixes_constructed_types] *)
Lemma V_semi (Var : Set) : semi :: (V : Code Var).
Proof.
  apply V_fixes_closure;
  split; [apply semi_nondecreasing | apply semi_idempotent].
Qed.
Hint Rewrite V_semi : code_simpl.

Ltac A_fixes :=
  let r := fresh "r" in
  let s := fresh "s" in
  let Hsr := fresh "H" s r in
  match goal with
    | [Var : Set |- _ :: ?a] =>

      fold (@A Var); split;
      [ apply A_fixes; intros r s Hsr; unfold a
      | rewrite <- V_semi; unfold a; auto]
  end.

Lemma semi_inhab_bot (Var : Set) : BOT :: (semi : Code Var).
Proof.
  fold (@A Var); split.
    apply A_fixes; intros r s Hsr; unfold semi.
    eta_expand; code_simpl.
    rewrite (code_le_bot _ (r * BOT)) at 1.
    rewrite <- beta_b.
    rewrite Hsr; auto.
  rewrite <- semi_nondecreasing; beta_simpl; auto.
Qed.
Hint Rewrite semi_inhab_bot : code_simpl.

Lemma semi_inhab_i (Var : Set) : I :: (semi : Code Var).
Proof.
  fold (@A Var); split.
    apply A_fixes; intros r s Hsr; unfold semi.
    eta_expand; code_simpl.
    rewrite <- beta_b.
    rewrite Hsr; code_simpl; auto.
  rewrite <- semi_nondecreasing; beta_simpl; auto.
Qed.
Hint Rewrite semi_inhab_i : code_simpl.

Lemma semi_inhab_top (Var : Set) : TOP :: (semi : Code Var).
Proof.
  rewrite <- V_semi; apply V1_inhab_top.
Qed.
Hint Rewrite semi_inhab_top : code_simpl.

Inductive semi_fixes {Var : Set} : Code Var -> Prop :=
  | semi_fixes_eq x y : x == y -> semi_fixes x -> semi_fixes y
  | semi_fixes_bot : semi_fixes BOT
  | semi_fixes_i : semi_fixes I
  | semi_fixes_top : semi_fixes TOP.
Hint Constructors semi_fixes.

Instance semi_fixes_proper (Var : Set) :
  Proper (code_eq ==> iff) (@semi_fixes Var).
Proof.
  intros x y xy; split; [idtac | apply symmetry in xy];
  intro H; induction H; eauto.
Qed.

(* main theorem *)

Theorem semi_sound (Var : Set) (x : Code Var) : x :: semi -> semi_fixes x.
Proof.
  intros H.
  case_le (x [= BOT) as Hbot.
    assert (x == BOT) as eq; [split; auto|].
    rewrite eq; auto.
  case_le (x [= I) as Hi.
    assert (x == I) as eq; [split; [|rewrite <- H; apply A_repairs]; auto|].
    rewrite eq; auto.
  assert (x == TOP) as eq; [split; [|rewrite <- H; apply A_raises]; auto|].
  rewrite eq; auto.
Qed.

Theorem semi_inhab (Var : Set) (x : Code Var) : x :: semi <-> semi_fixes x.
Proof.
  split.
    apply semi_sound.
  intro H; induction H; code_simpl; auto.
  rewrite <- H; auto.
Qed.

(* ------------------------------------------------------------------------ *)
(** ** [boool] is the type of ambiguous boolean values *)
(** [boool] is inhabited by [K], [F], and [J].
    We will later define a stricter [bool] that raises [J] to [TOP],
    i.e., raising an error on ambiguous values. *)

Section boool.
  Context {Var : Set}.
  Let a := make_var Var 0.
  Let a' := make_var Var 1.
  Definition boool := Eval compute in close_var (\\a,a'; a --> a --> a').
End boool.

Lemma boool_nondecreasing (Var : Set) : I [= (boool : Code Var).
Proof.
  unfold boool.
  eta_expand.
  rewrite code_eq_y.
  rewrite pi_j_left.
  rewrite beta_k.
  rewrite beta_j_ap.
  repeat rewrite pi_j_left.
  beta_simpl.
  beta_eta.
Qed.

Lemma boool_idempotent (Var : Set) : boool o boool == (boool : Code Var).
Proof.
  eta_expand as a; rewrite beta_b.
Admitted.
Hint Rewrite boool_idempotent : code_simpl.

Lemma V_boool (Var : Set) : boool :: (V : Code Var).
Proof.
  apply V_fixes_closure;
  split; [apply boool_nondecreasing | apply boool_idempotent].
Qed.
Hint Rewrite V_boool : code_simpl.

Lemma boool_inhab_bot (Var : Set) : BOT :: (boool : Code Var).
Proof.
  fold (@A Var); split.
    apply A_fixes; intros r s Hsr; unfold boool.
    eta_expand; eta_expand; rewrite beta_s; code_simpl.
    rewrite (code_le_bot _ (r * BOT)) at 1.
    rewrite <- beta_b.
    rewrite Hsr; auto.
  auto.
Qed.
Hint Rewrite boool_inhab_bot : code_simpl.

Lemma boool_inhab_k (Var : Set) : K :: (boool : Code Var).
Proof.
  fold (@A Var); split.
    apply A_fixes; intros r s Hsr; unfold boool.
    eta_expand; eta_expand; rewrite beta_s; code_simpl.
    rewrite <- beta_b.
    rewrite Hsr; auto.
  rewrite <- boool_nondecreasing; beta_eta.
Qed.
Hint Rewrite boool_inhab_k : code_simpl.

Lemma boool_inhab_f (Var : Set) : K * I :: (boool : Code Var).
Proof.
  fold (@A Var); split.
    apply A_fixes; intros r s Hsr; unfold boool.
    eta_expand; eta_expand; rewrite beta_s; code_simpl.
    rewrite <- beta_b.
    rewrite Hsr; auto.
  rewrite <- boool_nondecreasing; beta_eta.
Qed.
Hint Rewrite boool_inhab_f : code_simpl.

Lemma boool_inhab_j (Var : Set) : J :: (boool : Code Var).
Proof.
  fold (@A Var); split.
    apply A_fixes; intros r s Hsr; unfold boool.
    eta_expand; eta_expand; rewrite beta_s; code_simpl.
    rewrite code_le_j_ap_right.
    rewrite <- beta_b.
    rewrite Hsr; auto.
  rewrite <- boool_nondecreasing; beta_eta.
Qed.
Hint Rewrite boool_inhab_j : code_simpl.

Lemma boool_inhab_top (Var : Set) : TOP :: (boool : Code Var).
Proof.
  rewrite <- V_boool; apply V1_inhab_top.
Qed.
Hint Rewrite boool_inhab_top : code_simpl.

Inductive boool_fixes {Var : Set} : Code Var -> Prop :=
  | boool_fixes_eq x y : x == y -> boool_fixes x -> boool_fixes y
  | boool_fixes_bot : boool_fixes BOT
  | boool_fixes_k : boool_fixes K
  | boool_fixes_f : boool_fixes (K * I)
  | boool_fixes_j : boool_fixes J
  | boool_fixes_top : boool_fixes TOP.
Hint Constructors boool_fixes.

Instance boool_fixes_proper (Var : Set) :
  Proper (code_eq ==> iff) (@boool_fixes Var).
Proof.
  intros x y xy; split; [idtac | apply symmetry in xy];
  intro H; induction H; eauto.
Qed.

Theorem boool_sound (Var : Set) (x : Code Var) : x :: boool -> boool_fixes x.
Proof.
  intros H.
  case_le (x [= BOT) as Hbot.
    assert (x == BOT) as eq.
      split; auto.
    rewrite eq; auto.
  (* TODO adapt this argument from semi:
  case_le (x [= I) as Hi.
    assert (x == I) as eq.
      split; [|rewrite <- H; apply A_repairs]; auto.
    rewrite eq; auto.
  assert (x == TOP) as eq.
    split; [|rewrite <- H; apply A_raises]; auto.
  rewrite eq; auto.
  *)
Admitted.

Theorem boool_inhab (Var : Set) (x : Code Var) : x :: boool <-> boool_fixes x.
Proof.
  split.
    apply boool_sound.
  intro H; induction H; code_simpl; auto.
  rewrite <- H; auto.
Qed.

(* ------------------------------------------------------------------------ *)
(** ** [bool] is a disambiguated subtype of [boool] *)
(** We narrow the [boool] type to [bool] by disambiguating the unwanted
    inhabitants *)

Section bool.
  Context {Var : Set}.
  Let f := make_var Var 0.
  Let disambiguate := Eval compute in close_var
    (\f, f * (f * K * TOP) * (f * TOP * (K * I))).
  Definition bool := Eval compute in (P * boool * disambiguate).
End bool.

Lemma bool_nondecreasing (Var : Set) : I [= (bool : Code Var).
Proof.
  apply P2_nondecreasing.
Qed.

Lemma bool_idempotent (Var : Set) : bool o bool == (bool : Code Var).
Proof.
  apply P2_idempotent.
Qed.
Hint Rewrite bool_idempotent : code_simpl.

Lemma V_bool (Var : Set) : bool :: (V : Code Var).
Proof.
  apply V_P2.
Qed.
Hint Rewrite V_bool : code_simpl.

Lemma bool_inhab_bot (Var : Set) : BOT :: (bool : Code Var).
Proof.
  unfold bool; fold (@P Var); fold (@boool Var).
  apply P2_inhab_le;
  split; [ apply boool_inhab_bot | beta_reduce; code_simpl; auto ].
Qed.
Hint Rewrite bool_inhab_bot : code_simpl.

Lemma bool_inhab_k (Var : Set) : K :: (bool : Code Var).
Proof.
  unfold bool; fold (@P Var); fold (@boool Var).
  apply P2_inhab_le;
  split; [ apply boool_inhab_k | beta_reduce; code_simpl; auto ].
Qed.
Hint Rewrite bool_inhab_k : code_simpl.

Lemma bool_inhab_f (Var : Set) : K * I :: (bool : Code Var).
Proof.
  unfold bool; fold (@P Var); fold (@boool Var).
  apply P2_inhab_le;
  split; [ apply boool_inhab_f | beta_reduce; code_simpl; auto ].
Qed.
Hint Rewrite bool_inhab_f : code_simpl.

Lemma bool_inhab_top (Var : Set) : TOP :: (bool : Code Var).
Proof.
  rewrite <- V_bool; apply V1_inhab_top.
Qed.
Hint Rewrite bool_inhab_top : code_simpl.

Lemma bool_j_top (Var : Set) : bool * J == (TOP : Code Var).
Proof.
  split; auto.
  unfold bool; fold (@boool Var); fold (@V Var); rewrite <- V_nondecreasing.
  beta_simpl; rewrite pi_j_right.
  rewrite beta_s; rewrite beta_s; code_simpl; auto.
Qed.
Hint Rewrite bool_j_top : code_simpl.

Inductive bool_fixes {Var : Set} : Code Var -> Prop :=
  | bool_fixes_eq x y : x == y -> bool_fixes x -> bool_fixes y
  | bool_fixes_bot : bool_fixes BOT
  | bool_fixes_k : bool_fixes K
  | bool_fixes_f : bool_fixes (K * I)
  | bool_fixes_top : bool_fixes TOP.
Hint Constructors bool_fixes.

Instance bool_fixes_proper (Var : Set) :
  Proper (code_eq ==> iff) (@bool_fixes Var).
Proof.
  intros x y xy; split; [idtac | apply symmetry in xy];
  intro H; induction H; eauto.
Qed.

Lemma code_nle_top_j (Var : Set) : ~ TOP [= (J : Code Var).
Proof.
  intro H.
  apply (code_le_ap_left _ _ _ BOT) in H.
  apply (code_le_ap_left _ _ _ BOT) in H.
  code_simpl in H.
  apply absolute_consistency in H; contradiction H.
Qed.

Theorem bool_sound (Var : Set) (x : Code Var) : x :: bool -> bool_fixes x.
Proof.
  intro H; set (H' := H);
  unfold bool in H'; fold (@boool Var) in H'; fold (@P Var) in H'.
  apply P2_fixes_simpl in H'; destruct H' as [Hb Hd].
  rewrite V_boool in Hb; rewrite boool_inhab in Hb; induction Hb; auto.
    rewrite <- H0 in *; apply IHHb; auto.
  code_simpl in H; destruct H as [H _].
  apply code_nle_top_j in H; contradiction H.
Qed.

Theorem bool_inhab (Var : Set) (x : Code Var) : x :: bool <-> bool_fixes x.
Proof.
  split.
    apply bool_sound.
  intro H; induction H; code_simpl; auto.
  rewrite <- H; auto.
Qed.

(* ------------------------------------------------------------------------ *)
(** Church numerals *)

Section fuzzy_nat.
  Context {Var : Set}.
  Let a := make_var Var 0.
  Let a' := make_var Var 1.
  Definition fuzzy_nat := Eval compute in close_var
    (\\a,a'; (a' --> a) --> a --> a').
End fuzzy_nat.

Section succ.
  Context {Var : Set}.
  Let n := make_var Var 0.
  Let f := make_var Var 1.
  Let x := make_var Var 2.
  Definition succ := Eval compute in close_var
    (\n, \f, \x, f * (n * f * x) || n * f * (f * x)).
  Definition zero := Eval compute in close_var (\f, \x, x).
End succ.

Section church_nat.
  Context {Var : Set}.
  Let disambiguate : Code Var := <<succ, zero>>.  (* does this work? *)
  Definition church_nat : Code Var := P * fuzzy_nat * disambiguate.
End church_nat.

(* ------------------------------------------------------------------------ *)
(** TODO: additional types

    - [Maybe]
    - [Prod]
    - [Sum]
    - [num]
    - [Stream]
*)
