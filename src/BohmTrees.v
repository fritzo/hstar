(** * Bohm Trees *)

Require Import Coq.Logic.Classical_Pred_Set.
Require Import Coq.Logic.Classical_Prop.
Require Import Coq.Program.Basics.
Require Import Coq.Program.Equality.
Require Import Coq.Setoids.Setoid.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Logic.Decidable.
Require Import Coq.Bool.Bool.
Require Import InformationOrdering.
Require Import Nontermination.
Require Export Compile.

(* TODO prove reflexive, transitive, etc. *)

(* ------------------------------------------------------------------------ *)
(** ** Bohm trees as normal forms *)

(** Bohm trees generalize the normal forms of pure lambda-calculus,
    where the language is extended by
    terms [BOT] and [TOP],
    reduction rules [BOT x -beta-> BOT] and [TOP x -beta-> TOP],
    and approximation rules [x -pi-> BOT] and [TOP -pi-> x].

    In the lambda-join-calculus, we also have
    terms [JOIN x y],
    a reduction rule [JOIN x y * z -beta-> JOIN (x * z) (y * z)],
    and three approximation rules:
    [z -pi-> x -> z -pi-> y -> z -pi-> JOIN x y]
    (or equivalently [x -pi-> JOIN x x]),
    [JOIN x y -pi-> x], and
    [JOIN x y -pi-> y].
    *)

Inductive normal {Var : Set} : Term Var -> Prop :=
  | normal_top : normal TOP
  | normal_bot : normal BOT
  | normal_join x y : normal x -> normal y -> normal (x || y)
  | normal_rand x y : normal x -> normal y -> normal (x (+) y)
  | normal_lambda x : @normal (option Var) x -> normal (LAMBDA x)
  | normal_inert x : inert x -> normal x
with inert {Var : Set} : Term Var -> Prop :=
  | inert_var v : inert (VAR v)
  | inert_app x y : inert x -> normal y -> inert (x * y).
Hint Constructors normal inert.

Lemma inert_normal (Var : Set) (x : Term Var) : inert x -> normal x.
Proof.
  intro H; induction H; eauto.
Qed.
Hint Resolve inert_normal.

Fixpoint normal_protect (Var : Set) (x : Term Var) (n : normal x) {struct n} :
  normal (term_protect x)
with inert_protect (Var : Set) (x : Term Var) (i : inert x) {struct i} :
  inert (term_protect x).
Proof.
  - induction n; unfold term_protect; simpl; fold (@term_protect Var); auto.
    + admit.  (* TODO use an option_map lemma or sth *)
  - induction i; unfold term_protect; simpl; fold (@term_protect Var); auto.
Admitted.
Hint Resolve normal_protect inert_protect.

Fixpoint is_normal {Var : Set} (w : Term Var) {struct w} : bool :=
  match w with
  | TOP => true
  | BOT => true
  | x || y => andb (is_normal x) (is_normal y)
  | x (+) y => andb (is_normal x) (is_normal y)
  | x * y => andb (is_inert x) (is_normal y)
  | term_var v => true
  | term_lambda x => is_normal x
  end
with is_inert {Var : Set} (w : Term Var) {struct w} : bool :=
  match w with
  | x * y => andb (is_inert x) (is_normal y)
  | term_var v => true
  | _ => false
  end.

Lemma is_inert_is_normal {Var : Set} (x : Term Var) :
  is_inert x = true -> is_normal x = true.
Proof.
  induction x; simpl; auto; intro H; inversion H.
Qed.

Fixpoint normal_is_normal {Var : Set} (x : Term Var) :
  normal x -> is_normal x = true
with inert_is_inert {Var : Set} (x : Term Var) :
  inert x -> is_inert x = true.
Proof.
  - clear normal_is_normal.
    intro H; induction H; simpl; auto.
    + rewrite IHnormal1, IHnormal2; simpl; auto.
    + rewrite IHnormal1, IHnormal2; simpl; auto.
    + apply is_inert_is_normal; apply inert_is_inert; auto.
  - clear inert_is_inert.
    intro H; induction H; simpl; auto.
    rewrite IHinert; simpl.
    auto using normal_is_normal.
Admitted.

Fixpoint normal_is_normal' {Var : Set} (x : Term Var) :
  is_normal x = true -> normal x
with inert_is_inert' {Var : Set} (x : Term Var) :
  is_inert x = true -> inert x.
Proof.
  - clear normal_is_normal'.
    dependent induction x; simpl; intros; eauto.
    + case_eq (is_normal x1); intro H1; rewrite H1 in H; simpl in H.
      apply normal_join; [apply IHx1 | apply IHx2]; auto.
      inversion H.
    + case_eq (is_normal x1); intro H1; rewrite H1 in H; simpl in H.
      apply normal_rand; [apply IHx1 | apply IHx2]; auto.
      inversion H.
  - clear inert_is_inert'.
    dependent induction x; simpl; intros; eauto; try inversion H.
    case_eq (is_inert x1); intro H2; rewrite H2 in H; simpl in H.
    apply inert_app; [apply IHx1 | try apply normal_is_normal']; auto.
    inversion H.
Admitted.

Lemma normal_is_normal_true {Var : Set} (x : Term Var) :
  normal x <-> is_normal x = true.
Proof.
  split; [apply normal_is_normal | apply normal_is_normal'].
Qed.

Lemma normal_is_normal_false {Var : Set} (x : Term Var) :
 ~ normal x <-> is_normal x = false.
Proof.
  case_eq (is_normal x); intros H; split; intro H'; auto.
  - rewrite normal_is_normal_true in H'; contradiction.
  - inversion H'.
  - rewrite normal_is_normal_true, H; auto.
Qed.

Ltac case_normal x :=
  let Hnx := fresh "Hn" x in
  case_eq (is_normal x);
  intro Hnx;
  [ rewrite <- normal_is_normal_true in Hnx
  | rewrite <- normal_is_normal_false in Hnx].

Lemma normal_decidable {Var : Set} (x : Term Var) : decidable (normal x).
Proof.
  unfold decidable; rewrite normal_is_normal_true; decide equality.
Qed.
Hint Resolve normal_decidable.

Ltac solve_normal :=
  match goal with
  | _ : _ |- normal _ => apply normal_is_normal_true; simpl; auto
  end.

Lemma normal_i (Var : Set) : normal (DeBruijn.I : Term Var).
Proof.
  solve_normal.
Qed.
Hint Resolve normal_i.

Lemma normal_k (Var : Set) : normal (DeBruijn.K : Term Var).
Proof.
  solve_normal.
Qed.
Hint Resolve normal_k.

Lemma normal_b (Var : Set) : normal (DeBruijn.B : Term Var).
Proof.
  solve_normal.
Qed.
Hint Resolve normal_b.

Lemma normal_c (Var : Set) : normal (DeBruijn.C : Term Var).
Proof.
  solve_normal.
Qed.
Hint Resolve normal_c.

Lemma normal_s (Var : Set) : normal (DeBruijn.S : Term Var).
Proof.
  solve_normal.
Qed.
Hint Resolve normal_s.

Lemma normal_j (Var : Set) : normal (DeBruijn.J : Term Var).
Proof.
  solve_normal.
Qed.
Hint Resolve normal_j.

Lemma normal_r (Var : Set) : normal (DeBruijn.R : Term Var).
Proof.
  solve_normal.
Qed.
Hint Resolve normal_r.

(** Bohm trees are normal forms WRT the following notion of reduction. *)

Inductive reduce {Var : Set} : relation (Term Var) :=
  | reduce_refl x : reduce x x
  | reduce_trans x y z : reduce x y -> reduce y z -> reduce x z
  | reduce_join_left x x' y : reduce x x' -> reduce (x || y) (x' || y)
  | reduce_join_right x y y' : reduce y y' -> reduce (x || y) (x || y')
  | reduce_rand_left x x' y : reduce x x' -> reduce (x (+) y) (x' (+) y)
  | reduce_rand_right x y y' : reduce y y' -> reduce (x (+) y) (x (+) y')
  | reduce_app_left x x' y : reduce x x' -> reduce (x * y) (x' * y)
  | reduce_app_right x y y' : reduce y y' -> reduce (x * y) (x * y')
  | reduce_lambda x x' :
      @reduce (option Var) x x' -> reduce (LAMBDA x) (LAMBDA x') 
  | reduce_top y : reduce (TOP * y) TOP
  | reduce_bot y : reduce (BOT * y) BOT
  | reduce_join_app x y z : reduce ((x || y) * z) (x * z || y * z)
  | reduce_rand_app x y z : reduce ((x (+) y) * z) (x * z (+) y * z)
  | reduce_lambda_app x y : reduce (term_lambda x * y) (lambda_app_sub x y).
Hint Constructors reduce.

Hint Rewrite
  @reduce_bot @reduce_join_app @reduce_rand_app @reduce_lambda_app
  : term_simpl.

Ltac term_simpl := autorewrite with term_simpl using simpl.

Instance reduce_reflexive (Var : Set) : Reflexive (@reduce Var) :=
  reduce_refl.

Instance reduce_transitive (Var : Set) : Transitive (@reduce Var) :=
  reduce_trans.

Instance term_join_proper_reduce (Var : Set) :
  Proper (reduce ==> reduce ==> reduce) (@term_join Var).
Proof.
  intros x x' xx' y y' yy'; transitivity (x' || y);
  [apply reduce_join_left | apply reduce_join_right]; assumption.
Qed.

Instance term_rand_proper_reduce (Var : Set) :
  Proper (reduce ==> reduce ==> reduce) (@term_rand Var).
Proof.
  intros x x' xx' y y' yy'; transitivity (x' (+) y);
  [apply reduce_rand_left | apply reduce_rand_right]; assumption.
Qed.

Instance term_app_proper_reduce (Var : Set) :
  Proper (reduce ==> reduce ==> reduce) (@term_app Var).
Proof.
  intros x x' xx' y y' yy'; transitivity (x' * y);
  [apply reduce_app_left | apply reduce_app_right]; assumption.
Qed.

Instance term_lambda_proper_reduce (Var : Set) :
  Proper (reduce ==> reduce) (@term_lambda Var) := reduce_lambda.

Instance reduce_eq_subrelation (Var : Set) : subrelation reduce (@term_eq Var).
Proof.
  unfold term_eq; intros x y xy; induction xy; simpl; auto.
  - transitivity (compile y); assumption.
  - rewrite IHxy; auto.
  - code_simpl; auto.
  - code_simpl; auto.
  - rewrite compile_lambda_app; auto.
Qed.

Fixpoint try_reduce_step {Var : Set} (x : Term Var) : option (Term Var) :=
  match x with
  | TOP * y => Some TOP
  | BOT * y => Some BOT
  | (x1 || x2) * y => Some (x1 * y || x2 * y)
  | (x1 (+) x2) * y => Some (x1 * y (+) x2 * y)
  | term_lambda x1 * x2 => Some (lambda_app_sub x1 x2)
  | l * r =>
      match try_reduce_step l with
      | Some l' => Some (l' * r)
      | None =>
          match try_reduce_step r with
          | Some r' => Some (l * r')
          | None => None
          end
      end
  | (l || r) =>
      match try_reduce_step l with
      | Some l' => Some (l' || r)
      | None =>
          match try_reduce_step r with
          | Some r' => Some (l || r')
          | None => None
          end
      end
  | l (+) r =>
      match try_reduce_step l with
      | Some l' => Some (l' (+) r)
      | None =>
          match try_reduce_step r with
          | Some r' => Some (l (+) r')
          | None => None
          end
      end
  | term_lambda y => 
      match try_reduce_step y with
      | Some y' => Some (LAMBDA y')
      | None => None
      end
  | _ => None
  end.

Section try_reduce_step_reduce.
  Local Ltac case_reduce x H :=
    let x' := fresh x "'" in
    let eq := fresh "E" x in
    case_eq (try_reduce_step x); [intros x' eq | intro eq];
    rewrite eq in H; simpl in H; auto.

  Lemma try_reduce_step_reduce (Var : Set) (x : Term Var) :
    match try_reduce_step x with
    | None => True
    | Some x' => reduce x x'
    end.
  Proof.
    induction x; simpl; auto.
    - case_reduce x1 IHx1; case_reduce x2 IHx2.
    - case_reduce x1 IHx1; case_reduce x2 IHx2.
    - case_reduce x1 IHx1;
      case_eq x1; intros; simpl; auto.
      + rewrite <- H; rewrite IHx1; reflexivity.
      + rewrite <- H; rewrite IHx1; reflexivity.
      + case_reduce x2 IHx2.
      + case_reduce x2 IHx2.
    - case_reduce x IHx.
  Qed.
End try_reduce_step_reduce.

Fixpoint is_irreducible {Var : Set} (x : Term Var) : bool :=
  match x with
  | TOP * _ => false
  | BOT * _ => false
  | (_ || _) * _ => false
  | (_ (+) _) * _ => false
  | term_lambda x1 * x2 => false
  | l * r => andb (is_irreducible l) (is_irreducible r)
  | l || r => andb (is_irreducible l) (is_irreducible r)
  | l (+) r => andb (is_irreducible l) (is_irreducible r)
  | term_lambda x1 => is_irreducible x1
  | _ => true
  end.

Definition is_none {a : Set} (x : option a) : bool :=
  match x with
  | None => true
  | Some _ => false
  end.

Section try_reduce_step_is_irreducible.
  Local Ltac case_some x H :=
    let x' := fresh x "'" in
    let Hx' := fresh x "'" in
    intros x' Hx';
    rewrite Hx' in H; simpl in H; rewrite H;
    simpl.

  Local Ltac case_none x H :=
    let Hx' := fresh x "'" in
    intro Hx';
    rewrite Hx' in H; simpl in H; rewrite H;
    simpl.

  Local Ltac cases_option x IHx :=
    case_eq (try_reduce_step x); [case_some x IHx | case_none x IHx].

  Local Ltac cases_option2 x1 x2 IHx1 IHx2 :=
    cases_option x1 IHx1;
    [ case x1; auto
    | cases_option x2 IHx2; case x1; auto
    ].

  Lemma try_reduce_step_is_irreducible {Var : Set} (x : Term Var) :
    is_irreducible x = is_none (try_reduce_step x).
  Proof.
    induction x; simpl; auto.
    - cases_option2 x1 x2 IHx1 IHx2.
    - cases_option2 x1 x2 IHx1 IHx2.
    - cases_option2 x1 x2 IHx1 IHx2.
    - cases_option x IHx; auto.
  Qed.
End try_reduce_step_is_irreducible.

Theorem is_irreducible_is_normal {Var : Set} (x : Term Var) :
  is_irreducible x = is_normal x.
Proof.
  induction x; simpl; auto.
  - rewrite IHx1; rewrite IHx2; clear IHx1 IHx2; revert x2.
    induction x1; simpl; auto.
  - rewrite IHx1; rewrite IHx2; clear IHx1 IHx2; simpl.
    case (is_normal x1); case (is_normal x2); simpl; reflexivity.
  - rewrite IHx1; rewrite IHx2; clear IHx1 IHx2; simpl.
    induction x1; auto.
Qed.


(* ------------------------------------------------------------------------ *)
(** ** Decidable properties of Bohm trees *)

Fixpoint normal_conv {Var : Set} (x : Term Var) : bool :=
  match x with
  | TOP => true
  | BOT => false
  | (x1 || x2) => orb (normal_conv x1) (normal_conv x2)
  | x1 (+) x2 => andb (normal_conv x1) (normal_conv x2)
  | x1 * x2 => normal_conv x1  (* assumes x is normal *)
  | term_lambda x => normal_conv x
  | term_var v => true
  end.

Lemma term_conv_normal_conv (Var : Set) (x : Term Var) :
  term_conv x <-> normal_conv x = true.
Proof.
Admitted.

Lemma term_conv_normal_conv' {Var : Set} (x : Term Var) :
 ~ term_conv x <-> normal_conv x = false.
Proof.
  case_eq (normal_conv x); intros H; split; intro H'; auto.
  - rewrite term_conv_normal_conv in H'; contradiction.
  - inversion H'.
  - rewrite term_conv_normal_conv, H; auto.
Qed.

Ltac case_normal_conv x :=
  let Hcx := fresh "Hc" x in
  case_eq (normal_conv x);
  intro Hcx;
  [ rewrite <- term_conv_normal_conv in Hcx
  | rewrite <- term_conv_normal_conv' in Hcx].

Lemma normal_conv_decidable (Var : Set) (x : Term Var) :
  normal x -> decidable (term_conv x).
Proof.
  unfold decidable; rewrite term_conv_normal_conv; decide equality.
Qed.
Hint Resolve normal_conv_decidable.

Definition normal_conv' {Var : Set} (x : Term Var) :
  normal x -> {term_conv x} + {~ term_conv x}.
Proof.
  intro Hn; case_normal_conv x; auto.
Defined.

Definition try_decide_conv {Var : Set} (x : Term Var) :
  {term_conv x} + {~ term_conv x} + {~normal x}.
Proof.
  case_normal x; [case_normal_conv x|]; auto.
Defined.

Fixpoint normal_pconv {Var : Set} (x : Term Var) : dyadic.
Admitted.

(* This uses beta-eta discrimination; do BTs have eta normal forms? *)
Fixpoint normal_is_le {Var : Set} (x y : Term Var) : bool.
Admitted.

Lemma normal_is_le_correct (Var : Set) (x y : Term Var) :
  normal x -> normal y ->
  if normal_is_le x y then x [= y else ~ x [= y.
Admitted.

Definition normal_is_le' {Var : Set} (x y : Term Var) :
  normal x -> normal y -> {x [= y} + {~ x [= y}.
Proof.
  intros Hnx Hny; set (H := normal_is_le_correct Var x y Hnx Hny).
  case_eq (normal_is_le x y); intro eq; rewrite eq in H; simpl in H;
  [apply left | apply right]; assumption.
Defined.

Definition normal_le {Var : Set} : relation (Term Var) :=
  fun x y => normal_is_le x y = true.

Lemma normal_is_le_le (Var : Set) (x y : Term Var) :
  normal x -> normal y -> (x [= y <-> normal_is_le x y = true).
Proof.
Admitted.

Lemma normal_is_le_le' {Var : Set} (x y : Term Var) :
  normal x -> normal y -> (~ x [= y <-> normal_is_le x y = false).
Proof.
  case_eq (normal_is_le x y); intros H; split; intro H'; auto.
  - rewrite normal_is_le_le in H'; auto; contradiction.
  - inversion H'.
  - rewrite normal_is_le_le, H; auto.
Qed.

Ltac case_normal_le x y :=
  let Hxy := fresh "H" x y in
  case_eq (normal_le x y);
  intro Hxy;
  [ rewrite <- normal_is_le_le in Hxy
  | rewrite <- normal_is_le_le' in Hxy].

Lemma normal_le_decidable (Var : Set) (x y : Term Var) :
  normal x -> normal y -> decidable (x [= y).
Proof.
  intros; unfold decidable; rewrite normal_is_le_le; auto; decide equality.
Qed.
Hint Resolve normal_le_decidable.

Definition try_decide_le (x y : ClosedTerm) :
  {x [= y} + {~ x [= y} + {~normal x \/ ~normal y}.
Proof.
  case_normal x; case_normal y; auto.
  apply inleft; apply normal_is_le'; auto.
Defined.


(* ------------------------------------------------------------------------ *)
(** ** Theorems about bohm trees and order *)

(** The [normal_dense] theorem motivates where to allow [JOIN] and [RAND]
    in Bohm trees.
    Whereas \cite{obermeyer2009automated} restricts [JOIN] and [RAND] to
    the argument of an [inert] variable,
    we here allow them at the top level
    to allow finite joins of dyadic mixtures.

    Question:
    Should [JOIN] and [RAND] be restricted to be inside lambda abstractions
    so as to force compatibility among proofs of repair and raise theorems?
    Consider the example

      \x y z. x <TOP> BOT (+) x BOT <TOP>

    What are the proof terms?
    *)

Theorem normal_dense {Var : Set} (x y : Term Var) :
  (forall x', normal x' -> x' [= x -> x' [= y) -> x [= y.
Proof.
Admitted.

(** Classically we can provide normal witnesses of non-ordering. *)

Lemma impl_not_impl_not (a b : Prop) : (~ b -> ~ a) <-> (a -> b).
Proof.
  apply contrapositive; apply classic.
Qed.

Corollary nle_normal_witness {Var : Set} (x y : Term Var) :
  ~ x [= y ->
  exists x', normal x' /\ x' [= x /\
  ~ x' [= y.
Proof.
  intro Hxy.
  set (H := normal_dense x y); apply impl_not_impl_not in H; auto.
  apply not_all_ex_not in H; destruct H as [x' H]; exists x'.
  repeat split; auto.
  - apply not_imply_elim in H; assumption.
  - apply not_imply_elim2 in H; apply not_imply_elim in H; assumption.
Qed.
