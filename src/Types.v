(** * Types as closures *)

Require Import Coq.Classes.Morphisms.
Require Export TypeConstructor.
Require Import Nontermination.
Require Import LeastFixedPoint.
Require Import BohmTrees.
Open Scope code_scope.

(** ** Properties of types *)

Definition closure {Var : Set} (a : Code Var) := I [= a /\ a o a == a.
Definition fixes {Var : Set} (a : Code Var) (x : Code Var) := a * x == x.
Notation "x :: a" := (fixes a x) : code_scope.

Instance closure_proper_eq (Var : Set) :
  Proper (code_eq ==> iff) (@closure Var).
Proof.
  simpl_relation; unfold closure; split; intros [Hn Hi]; split;
  (rewrite -> H || rewrite <- H); auto.
Qed.

Instance fixes_proper_eq (Var : Set) :
  Proper (code_eq ==> code_eq ==> iff) (@fixes Var).
Proof.
  unfold fixes; intros a a' Ha x x' Hx.
  rewrite Ha; rewrite Hx; firstorder.
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
(** ** [I] is the largest type, the type of everyting *)

Lemma I_nondecreasing (Var : Set) : I [= (I : Code Var).
Proof. auto. Qed.

Lemma I_idempotent (Var : Set) : I o I == (I : Code Var).
Proof. beta_eta. Qed.
Hint Rewrite I_idempotent.

Lemma I_closure {Var : Set} : closure (I : Code Var).
Proof.
  split; [apply I_nondecreasing | apply I_idempotent].
Qed.

Inductive I_fixes {Var : Set} : Code Var -> Prop :=
  I_fixes_intro x : I_fixes x.
Hint Constructors I_fixes.

Instance I_fixes_proper (Var : Set) : Proper (code_eq ==> iff) (@I_fixes Var).
Proof.
  simpl_relation; auto.
Qed.

Theorem I_inhab (Var : Set) (x : Code Var) : x :: I <-> I_fixes x.
Proof.
  unfold fixes; beta_reduce; firstorder.
Qed.

(* ------------------------------------------------------------------------ *)
(** ** [V] is the type of all types *)

Lemma V_nondecreasing (Var : Set) : I [= (V : Code Var).
Proof.
  eta_expand as a.
  rewrite beta_v; rewrite pi_j_right.
  rewrite beta_v; rewrite pi_j_left.
  beta_eta.
Qed.

Lemma V_idempotent (Var : Set) : V o V == (V : Code Var).
Proof.
  apply nondecreasing_idempotent.
    apply V_nondecreasing.
  eta_expand as a; rewrite beta_b.
Admitted.
Hint Rewrite V_idempotent.

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
  unfold fixes, closure.
  intros Hfix; apply V_fixes_intro.
  assert (I [= x).
    rewrite <- Hfix; rewrite beta_v; auto.
  split; auto.
  rewrite <- Hfix at 3; rewrite beta_v; rewrite Hfix.
  split; auto.
  apply code_le_j_ub; auto.
  rewrite <- I_idempotent.
  monotonicity; auto.
Qed.

Lemma V_complete (Var : Set) (x : Code Var) : V_fixes x -> x :: V.
Proof.
  unfold fixes, closure; intros [Hn Hi].
  (* TODO this requires a least fixed point lemma *)
Admitted.

Theorem V_inhab (Var : Set) (x : Code Var) : x :: V <-> V_fixes x.
Proof.
  split; [apply V_sound | apply V_complete].
Qed.

Corollary fixes_V_V (Var : Set) : fixes V (V : Code Var).
Proof.
  apply V_inhab; apply V_fixes_intro; apply V_closure.
Qed.

(* ------------------------------------------------------------------------ *)
(** Next some lemmas about inhabinants of V. *)

Lemma V1_nondecreasing (Var : Set) (a : Code Var) : I [= V * a.
Proof.
Admitted.

Lemma V1_idempotent (Var : Set) (a : Code Var) : (V * a) o (V * a) == (V * a).
Admitted.
Hint Rewrite V1_idempotent.

Lemma V1_closure (Var : Set) (a : Code Var) : closure (V * a).
Proof.
Admitted.

(* ------------------------------------------------------------------------ *)
(** ** [P] is a powertype operator *)

(** [P] acts as both a unary subtype operation
    and a binary type intersection operation.
    We start with the unary version. *)

Section P.
  Context {Var : Set}.
  Let a := make_var Var 0.
  Let a' := make_var Var 1.
  Definition P := Eval compute in close (\a, \a', V * (a || a')).
End P.

Lemma P_idem (Var : Set) (a : Code Var) : P * a * a == V * a.
Proof.
  (* OLD
  unfold P; beta_simpl; rewrite code_eq_j_idem; auto.
  *)
Admitted.
Hint Rewrite P_idem.

Lemma P_comm (Var : Set) (a b : Code Var) : P * a * b == P * b * a.
Proof.
Admitted.

Lemma P_assoc (Var : Set) (a b c : Code Var) :
  P * a * (P * b * c) == P * (P * a * b) * c.
Proof.
Admitted.

Lemma P1_nondecreasing (Var : Set) (a : Code Var) : I [= P * a.
Proof.
  unfold P.
  eta_expand as a'; rewrite beta_b; rewrite beta_b; rewrite pi_j_right.
  monotonicity; apply V_nondecreasing.
Qed.

Lemma P1_idempotent (Var : Set) (a : Code Var) : (P * a) o (P * a) == P * a.
Proof.
  apply nondecreasing_idempotent.
    apply P1_nondecreasing.
  eta_expand as a'; rewrite beta_b.
Admitted.
Hint Rewrite P1_idempotent.

Lemma P1_closure (Var : Set) (a : Code Var): closure (P * a).
Proof.
  split; [apply P1_nondecreasing | apply P1_idempotent].
Qed.

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
  unfold fixes, closure, P; beta_simpl.
  intros Hfix.
  assert (I [= x).
  (* OLD
    rewrite <- Hfix; rewrite beta_v; auto.
  split; auto.
  *)
  (* TODO adapt proof from V:
  rewrite <- Hfix at 3; rewrite beta_v; rewrite Hfix.
  split; auto.
  apply code_le_j_ub; auto.
  rewrite <- I_idempotent.
  monotonicity; auto.
  *)
Admitted.

Lemma P1_complete (Var : Set) (a x : Code Var) : P1_fixes a x -> x :: P * a.
Proof.
  unfold fixes, closure; intros [Hn Hi].
  (* TODO this requires a least fixed point lemma *)
Admitted.

Theorem P1_inhab (Var : Set) (a x : Code Var) : x :: P * a <-> P1_fixes a x.
Proof.
  split; [apply P1_sound | apply P1_complete].
Qed.

Lemma P1_idem (Var : Set) (a : Code Var) : V_fixes a -> P1_fixes a a.
Proof.
  intros H; apply P1_fixes_intro; auto.
Qed.

(* ------------------------------------------------------------------------ *)
(** Next we treat [P] as a binary type intersection operation. *)

Lemma P2_nondecreasing (Var : Set) (a b : Code Var) : I [= P * a * b.
Proof.
  (* OLD
  unfold P; beta_simpl; apply V1_nondecreasing.
  *)
Admitted.

Lemma P2_idempotent (Var : Set) (a b : Code Var) :
  (P * a * b) o (P * a * b) == P * a * b.
Proof.
  (* OLD
  unfold P; beta_simpl; apply V1_idempotent.
  *)
Admitted.
Hint Rewrite P1_idempotent.

Lemma P2_closure (Var : Set) (a b : Code Var): closure (P * a * b).
Proof.
  (* OLD
  unfold P; beta_simpl; apply V1_closure.
  *)
Admitted.

Inductive P2_fixes {Var : Set} (a b : Code Var) : Code Var -> Prop :=
  P2_fixes_intro x : x :: V * a -> x :: V * b -> P2_fixes a b x.
  (* Which of these forms is most convenient?
  P2_fixes_intro x : a * x [= x -> b * x [= x -> P2_fixes a b x.
  *)

Instance P2_fixes_proper (Var : Set) :
  Proper (code_eq ==> code_eq ==> code_eq ==> iff) (@P2_fixes Var).
Proof.
  intros a a' aa' b b' bb' x x' xx'; split; intro Ha.
Admitted.

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
Hint Rewrite div_idempotent.

Lemma div_closure {Var : Set} : closure (div : Code Var).
Proof.
  split; [apply div_nondecreasing | apply div_idempotent].
Qed.

Lemma div_inhab_bot (Var : Set) : BOT :: (div : Code Var).
Proof.
  apply div_bot.
Qed.

Lemma div_inhab_top (Var : Set) : TOP :: (div : Code Var).
Proof.
  unfold fixes; split; auto.
  rewrite <- div_nondecreasing; rewrite beta_i; auto.
Qed.

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
  intros H; unfold fixes in H.
  (* requires a branch on [conv x] *)
Admitted.

Theorem div_inhab (Var : Set) (x : Code Var) : x :: div <-> div_fixes x.
Proof.
  split.
    apply div_sound.
  intro H; induction H.
  rewrite <- H; auto.
  apply div_inhab_bot.
  apply div_inhab_top.
Qed.

(* We also have an algebraic definition of [div] as nil *)

Section div'.
  Context {Var : Set}.
  Let a := make_var Var 0.
  Let a' := make_var Var 1.
  Definition div' := Eval compute in close (\\a,a'; a').
End div'.

Lemma div_algebraic (Var : Set) : div' == (div : Code Var).
Proof.
  unfold div, div'; code_simpl.
Admitted.

(* ------------------------------------------------------------------------ *)
(** ** [semi] is Sierpinsky space, inhabited by [{BOT, I, TOP}] *)

Section semi.
  Context {Var : Set}.
  Let a := make_var Var 0.
  Let a' := make_var Var 1.
  Definition semi := Eval compute in close (\\a,a'; a --> a').
End semi.

Lemma semi_nondecreasing (Var : Set) : I [= (semi : Code Var).
Proof.
  unfold semi.
  eta_expand as a.
  rewrite beta_y; rewrite pi_j_left.
  rewrite beta_j_ap.
  repeat rewrite pi_j_left.
  beta_simpl.
  beta_eta.
Qed.

Lemma semi_idempotent (Var : Set) : semi o semi == (semi : Code Var).
Proof.
  eta_expand as a; rewrite beta_b.
  (* TODO this requires a least-fixed-point argument *)
Admitted.
Hint Rewrite semi_idempotent.

Lemma semi_closure {Var : Set} : closure (semi : Code Var).
Proof.
  split; [apply semi_nondecreasing | apply semi_idempotent].
Qed.

Lemma semi_inhab_bot (Var : Set) : BOT :: (semi : Code Var).
Proof.
Admitted.

Lemma semi_inhab_i (Var : Set) : I :: (semi : Code Var).
Proof.
  (* TODO this requires a least-fixed-point argument *)
Admitted.

Lemma semi_inhab_top (Var : Set) : TOP :: (semi : Code Var).
Proof.
Admitted.

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

Theorem semi_sound (Var : Set) (x : Code Var) :
  x :: semi -> semi_fixes x.
Proof.
  intros H; unfold fixes in H.
  (* TODO this requires a Bohm-tree argument *)
Admitted.

Theorem semi_inhab (Var : Set) (x : Code Var) : x :: semi <-> semi_fixes x.
Proof.
  split.
    apply semi_sound.
  intro H; induction H.
  rewrite <- H; auto.
  apply semi_inhab_bot.
  apply semi_inhab_i.
  apply semi_inhab_top.
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
  Definition boool := Eval compute in close (\\a,a'; a --> a --> a').
End boool.

Lemma boool_nondecreasing (Var : Set) : I [= (boool : Code Var).
Proof.
  unfold boool.
  eta_expand as a.
  rewrite beta_y; rewrite pi_j_left.
  rewrite beta_j_ap.
  repeat rewrite pi_j_left.
  beta_simpl.
  beta_eta.
Qed.

Lemma boool_idempotent (Var : Set) : boool o boool == (boool : Code Var).
Proof.
  eta_expand as a; rewrite beta_b.
Admitted.
Hint Rewrite boool_idempotent.

Lemma boool_closure {Var : Set} : closure (boool : Code Var).
Proof.
  split; [apply boool_nondecreasing | apply boool_idempotent].
Qed.

Lemma boool_inhab_bot (Var : Set) : BOT :: (boool : Code Var).
Proof.
Admitted.

Lemma boool_inhab_k (Var : Set) : K :: (boool : Code Var).
Proof.
Admitted.

Lemma boool_inhab_f (Var : Set) : K * I :: (boool : Code Var).
Proof.
Admitted.

Lemma boool_inhab_j (Var : Set) : J :: (boool : Code Var).
Proof.
Admitted.

Lemma boool_inhab_top (Var : Set) : TOP :: (boool : Code Var).
Proof.
Admitted.

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
  intros H; unfold fixes in H.
Admitted.

Theorem boool_inhab (Var : Set) (x : Code Var) : x :: boool <-> boool_fixes x.
Proof.
  split.
    apply boool_sound.
  intro H; induction H.
  rewrite <- H; auto.
  apply boool_inhab_bot.
  apply boool_inhab_k.
  apply boool_inhab_f.
  apply boool_inhab_j.
  apply boool_inhab_top.
Qed.

(* ------------------------------------------------------------------------ *)
(** ** [bool] is a disambiguated subtype of [boool] *)
(** We narrow the [boool] type to [bool] by disambiguating the unwanted
    inhabitants *)

Section bool.
  Context {Var : Set}.
  Let f := make_var Var 0.
  Let disambiguate := Eval compute in close
    (\f, f * (f * K * TOP) * (f * TOP * (K * I))).
  Definition bool := Eval compute in (P * boool * disambiguate).
End bool.

Lemma bool_nondecreasing (Var : Set) : I [= (bool : Code Var).
Proof.
Admitted.

Lemma bool_idempotent (Var : Set) : bool o bool == (bool : Code Var).
Proof.
  eta_expand as a; rewrite beta_b.
Admitted.
Hint Rewrite bool_idempotent.

Lemma bool_closure {Var : Set} : closure (bool : Code Var).
Proof.
  split; [apply bool_nondecreasing | apply bool_idempotent].
Qed.

Lemma bool_inhab_bot (Var : Set) : BOT :: (bool : Code Var).
Proof.
Admitted.

Lemma bool_inhab_k (Var : Set) : K :: (bool : Code Var).
Proof.
Admitted.

Lemma bool_inhab_f (Var : Set) : K * I :: (bool : Code Var).
Proof.
Admitted.

Lemma bool_inhab_top (Var : Set) : TOP :: (bool : Code Var).
Proof.
Admitted.

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

Theorem bool_sound (Var : Set) (x : Code Var) : x :: bool -> bool_fixes x.
Proof.
  intros H; unfold fixes in H.
Admitted.

Theorem bool_inhab (Var : Set) (x : Code Var) : x :: bool <-> bool_fixes x.
Proof.
  split.
    apply bool_sound.
  intro H; induction H.
  rewrite <- H; auto.
  apply bool_inhab_bot.
  apply bool_inhab_k.
  apply bool_inhab_f.
  apply bool_inhab_top.
Qed.

(* ------------------------------------------------------------------------ *)
(** Church numerals *)

Section fuzzy_nat.
  Context {Var : Set}.
  Let a := make_var Var 0.
  Let a' := make_var Var 1.
  Definition fuzzy_nat := Eval compute in (\\a,a'; (a' --> a) --> a --> a').
End fuzzy_nat.

Section succ.
  Context {Var : Set}.
  Let n := make_var Var 0.
  Let f := make_var Var 1.
  Let x := make_var Var 2.
  Definition succ := Eval compute in close
    (\n, \f, \x, f * (n * f * x) || n * f * (f * x)).
  Definition zero := Eval compute in close (\f, \x, x).
End succ.

(* TODO: how to disambiguate [nat]? *)

(* ------------------------------------------------------------------------ *)
(** TODO: additional types

    - [Maybe]
    - [Prod]
    - [Sum]
    - [num]
    - [Stream]
*)
