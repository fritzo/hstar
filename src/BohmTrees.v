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

Definition term_conv {Var : Set} (t : Term Var) := code_conv (compile t).
Definition term_le {Var : Set} (x y : Term Var) := compile x [= compile y.
Definition term_eq {Var : Set} (x y : Term Var) := compile x == compile y.

Notation "x == y" := (term_eq x y)%term : term_scope.
Notation "x [= y" := (term_le x y)%term : term_scope.
Notation "x :: a" := (term_app a x == x)%term : term_scope.

(* TODO prove reflexive, transitive, etc. *)

(** Bohm trees generalize the normal forms of pure lambda-calculus,
    where the language is extended by
    a term [BOT],
    a reduction rule [BOT x -beta-> BOT],
    and an approximation rule [x -pi-> BOT].

    In the lambda-join-calculus, we also have
    terms [JOIN x y],
    a reduction rule [JOIN x y * z -beta-> JOIN (x * z) (y * z)],
    and three approximation rules:
    [z -pi-> x -> z -pi-> y -> z -pi-> JOIN x y]
    (or equivalently [x -pi-> JOIN x x]),
    [JOIN x y -pi-> x], and
    [JOIN x y -pi-> y].
    We also add an identifiable top term [TOP] with
    a reduction rule [TOP x -beta-> TOP],
    and an approximation rule [TOP -pi-> x].
    (This last rule [TOP -pi-> x] is hard to motivate; should it be dropped?)
    *)

Inductive normal {Var : Set} : Term Var -> Prop :=
  | normal_top : normal TOP
  | normal_bot : normal BOT
  | normal_join x y : normal x -> normal y -> normal (x || y)
  | normal_rand x y : normal x -> normal y -> normal (x (+) y)
  | normal_app x y : inert x -> normal y -> normal (x * y)
  | normal_lambda x : @normal (option Var) x -> normal (LAMBDA x)
  | normal_var v : normal (VAR v)
with inert {Var : Set} : Term Var -> Set :=
  | inert_var v : inert (VAR v)
  | inert_app x y : inert x -> normal y -> inert (x * y).
Hint Constructors normal inert.

Lemma inert_normal {Var : Set} (x : Term Var) : inert x -> normal x.
Proof.
  intro H; induction H; eauto.
Qed.

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

Lemma normal_is_normal {Var : Set} (x : Term Var) :
 normal x <-> is_normal x = true.
Proof.
  split.
  - intro H; induction H; simpl; auto.
    + rewrite IHnormal1; rewrite IHnormal2; simpl; auto.
    + rewrite IHnormal1; rewrite IHnormal2; simpl; auto.
    + rewrite IHnormal; simpl; auto.
      admit.
  - dependent induction x; simpl; intros; eauto.
    + revert H;
      (* FIXME need to simultaneously do induction on inert and normal
      case_eq (is_inert x1); case_eq (is_normal x2); simpl;
      intros Ex2 Ex1 H; destruct H; auto.
      apply is_inert_is_normal in Ex1.
      rewrite Ex1 in IHx1; rewrite Ex2 in IHx2; simpl.
      *)
      admit.
    + admit.
    + admit.
Qed.

Lemma normal_decidable {Var : Set} (x : Term Var) : decidable (normal x).
Proof.
  unfold decidable; rewrite normal_is_normal; decide equality.
Qed.

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

(** Many properties of Bohm trees are decidable *)

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

Lemma normal_conv_correct (Var : Set) (x : Term Var) :
  if normal_conv x then term_conv x else ~ term_conv x.
Proof.
  induction x; simpl; auto.
Admitted.

Definition normal_conv' {Var : Set} (x : Term Var) :
  normal x -> {term_conv x} + {~ term_conv x}.
Proof.
  intro Hn.
  set (H := normal_conv_correct Var x).
  case_eq (normal_conv x); intro Hc; rewrite Hc in H; simpl in H;
  [ apply left | apply right]; assumption.
Defined.

Definition try_decide_conv {Var : Set} (x : Term Var) :
  {term_conv x} + {~ term_conv x} + {~normal x}.
Proof.
  case_eq (is_normal x); intro Hn.
  - apply normal_is_normal in Hn.
    apply inleft; apply normal_conv'; auto.
  - assert (~ is_normal x = true) as Hn'.
      rewrite Hn; auto.
    assert (~ normal x) as Hc'.
      intro Hc'; apply normal_is_normal in Hc'; contradiction.
    apply inright; auto.
Defined.


Inductive dyadic : Set :=
  | dyadic_one : dyadic
  | dyadic_zero : dyadic
  | dyadic_rand : dyadic -> dyadic -> dyadic.

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

Fixpoint try_decide_le (x y : ClosedTerm) :
  {x [= y} + {~ x [= y} + {~normal x \/ ~normal y}.
Admitted.

(** ** Theorems about bohm trees and order *)

(** The [normal_dense] theorem motivates where to allow [JOIN] and [RAND]
    in Bohm trees.
    Whereas \cite{obermeyer2009automated} restricts [JOIN] and [RAND] to
    the argument of an [inert] variables,
    we here allow them at the top level
    to allow finite joins of dyadic mixtures.
    *)

Theorem normal_dense {Var : Set} (p q : Term Var) :
  (forall x, normal x -> p * x [= q * x) -> p [= q.
Admitted.

Corollary normal_dense_below {Var : Set} (x y : Term Var) :
  (forall x', normal x' -> x' [= x -> x' [= y) -> x [= y.
Proof.
Admitted.

Corollary normal_dense_above {Var : Set} (x y : Term Var) :
  (forall x', normal x' -> y [= x' -> x [= x') -> x [= y.
Admitted.


(** Classically we can provide normal witnesses of non-ordering. *)

Lemma prop_curry (a b c : Prop) : (a /\ b -> c) <-> (a -> b -> c).
Proof.
  firstorder.
Qed.

Lemma impl_not_impl_not (a b : Prop) : (~ b -> ~ a) <-> (a -> b).
Proof.
  apply contrapositive; apply classic.
Qed.

Corollary nle_normal_witness_left {Var : Set} (x y : Term Var) :
  ~ x [= y ->
  exists x', normal x' /\ x' [= x /\
  ~ x' [= y.
Proof.
  intro Hxy.
  set (H := normal_dense_below x y); apply impl_not_impl_not in H; auto.
  apply not_all_ex_not in H; destruct H as [x' H]; exists x'.
  repeat split; auto.
  - apply not_imply_elim in H; assumption.
  - apply not_imply_elim2 in H; apply not_imply_elim in H; assumption.
Qed.

Corollary nle_normal_witness_right {Var : Set} (x y : Term Var) :
  ~ x [= y ->
  exists y', normal y' /\ y [= y' /\
  ~ x [= y'.
Proof.
  intro Hxy.
  set (H := normal_dense_above x y); apply impl_not_impl_not in H; auto.
  apply not_all_ex_not in H; destruct H as [y' H]; exists y'.
  repeat split; auto.
  - apply not_imply_elim in H; assumption.
  - apply not_imply_elim2 in H; apply not_imply_elim in H; assumption.
Qed.

Corollary nle_normal_witnesses {Var : Set} (x y : Term Var) :
  ~ x [= y ->
  exists x', normal x' /\ x' [= x /\
  exists y', normal y' /\ y [= y' /\
  ~ x' [= y'.
Proof.
  intro xy.
  set (Hx := nle_normal_witness_left x y xy); destruct Hx as [x' [? [? xy']]].
  exists x'; split; auto; split; auto.
  set (Hy := nle_normal_witness_right x' y xy'); destruct Hy as [y' [? [? ?]]].
  exists y'; split; auto; split; auto.
Qed.
