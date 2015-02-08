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
Require Import DeBruijn.

(** Bohm trees generalize the normal forms of pure lambda-calculus,
    where the language is extended by
    a term [BOT],
    a reduction rule [BOT x -beta-> BOT],
    and an approximation rule [x -pi-> BOT].

    In the lambda-join-calculus, we also have
    terms [JOIN x y],
    a reduction rule [JOIN x y * z -beta-> JOIN (x * z) (y * z)],
    and three approximation rules:
    [x -pi-> z -> y -pi-z> -> JOIN x y -pi-> z],
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
  | inert_app x y : inert x -> normal y -> inert (x * y)
.
Hint Constructors normal inert.

Definition Normal (Var : Set) : Set := {x : Term Var | normal x}.

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
  | LAMBDA x => is_normal x
  | VAR v => true
  end
with is_inert {Var : Set} (w : Term Var) {struct w} : bool :=
  match w with
  | x * y => andb (is_inert x) (is_normal y)
  | VAR v => true
  | _ => false
  end.

Lemma is_inert_is_normal {Var : Set} (x : Term Var) :
  is_inert x = true -> is_normal x = true.
Proof.
  induction x; simpl; auto; intro H; inversion H.
Qed.

Definition if_true (b : bool) : Set := if b then unit else Empty_set. 
Definition if_false (b : bool) : Set := if b then Empty_set else unit. 

Notation "x <--> y" := ((x -> y) * (y -> x))%type
  (at level 95, no associativity).

Lemma normal_is_normal {Var : Set} (x : Term Var) :
 normal x <-> is_normal x = true.
(* normal x <--> is_normal x = true. *)
(* normal x <--> if_true (is_normal x). *)
(* normal x <-> is_normal x = true. *)
(* normal x <-> eq_true (is_normal x). *)
(* normal x <-> is_true (is_normal x). *)
(* normal x <-> Is_true (is_normal x). *)
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

Fixpoint try_reduce_step {Var : Set} (x : Term Var) : option (Term Var) :=
  match x with
  | TOP * y => Some TOP
  | BOT * y => Some BOT
  | (x1 || x2) * y => Some (x1 * y || x2 * y)
  | (x1 (+) x2) * y => Some (x1 * y (+) x2 * y)
  | LAMBDA x1 * x2 => Some (beta_sub x1 x2)
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
  | LAMBDA y => 
      match try_reduce_step y with
      | Some y' => Some (LAMBDA y')
      | None => None
      end
  | _ => None
  end.

Fixpoint is_irreducible {Var : Set} (x : Term Var) : bool :=
  match x with
  | TOP * _ => false
  | BOT * _ => false
  | (_ || _) * _ => false
  | (_ (+) _) * _ => false
  | LAMBDA x1 * x2 => false
  | l * r => andb (is_irreducible l) (is_irreducible r)
  | l || r => andb (is_irreducible l) (is_irreducible r)
  | l (+) r => andb (is_irreducible l) (is_irreducible r)
  | LAMBDA x1 => is_irreducible x1
  | _ => true
  end.

Definition is_none {a : Set} (x : option a) : bool :=
  match x with
  | None => true
  | Some _ => false
  end.

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

Fixpoint normal_conv {Var : Set} (x : Term Var) : normal x -> bool.
Admitted.

Inductive dyadic : Set :=
  | dyadic_one : dyadic
  | dyadic_zero : dyadic
  | dyadic_rand : dyadic -> dyadic -> dyadic.

Fixpoint normal_pconv {Var : Set} (x : Term Var) : normal x -> dyadic.
Admitted.

(* This uses beta-eta discrimination; do BTs have eta normal forms? *)
Fixpoint normal_is_le {Var : Set} (x y : Term Var) :
  normal x -> normal y -> bool.
Admitted.

Definition normal_is_eq
  {Var : Set} (x y : Term Var) (nx : normal x) (ny : normal y) : bool :=
  andb (normal_is_le x y nx ny) (normal_is_le y x ny nx).

Definition normal_le {Var : Set} : relation (Normal Var) :=
  fun xn => let (x, nx) := xn in
  fun yn => let (y, ny) := yn in
  normal_is_le x y nx ny = true.

Definition normal_eq {Var : Set} : relation (Normal Var) :=
  fun xn => let (x, nx) := xn in
  fun yn => let (y, ny) := yn in
  normal_is_eq x y nx ny = true.

(** ** Theorems about bohm trees and order *)

Definition term_le {Var : Set} : relation (Term Var). Admitted.
Definition term_eq {Var : Set} : relation (Term Var). Admitted.
Notation "x == y" := (term_eq x y) : term_scope.
Notation "x [= y" := (term_le x y) : term_scope.

(** The [normal_dense] theorem motivates where to allow [JOIN] and [RAND]
    in Bohm trees.
    Whereas \cite{obermeyer2009automated} restricts [JOIN] and [RAND] to
    the arguments of an [inert] variable,
    we here allow them at the top level
    to allow finite joins and dyadic mixtures.
    *)

Theorem normal_dense {Var : Set} (x y : Term Var) :
  (forall x', normal x' -> x' [= x -> x' [= y) -> x [= y.
Admitted.

Lemma prop_curry (a b c : Prop) : (a /\ b -> c) <-> (a -> b -> c).
Proof.
  firstorder.
Qed.

(** Classically we can provide normal witnesses of non-ordering. *)

Corollary nle_normal_witnesses {Var : Set} (x y : Term Var) :
  ~ x [= y ->
  exists x', normal x' /\ x [= x' /\
  exists y', normal y' /\ y' [= y' /\
  ~ x' [= y'.
Proof.
  intro H.
  (* OLD
  eapply ex_intro.
  rewrite <- and_assoc.
  apply imply_to_and.
  rewrite prop_curry.
  *)
  (* TODO undo eapply, then apply normal_dense
  apply ex_not_not_all.
  *)
Admitted.

(** Bohm's theorem construct from this witness a separating context. *)

Theorem Bohms_theorem (x y : Closed) :
  normal x -> normal y -> ~ x [= y ->
  exists c, TOP [= c * x /\ c * y [= BOT.
Proof.
  (* TODO use the Bohm-out method *)
Admitted.

(** Constructively, we can decide order among normal forms
    and discover a witness of non-ordering. *)

Fixpoint Bohms_program (x y : Closed) :
  normal x -> normal y -> 
  {witness : option Closed |
      match witness with
      | None => x [= y
      | Some c => TOP [= c * x /\ c * y [= BOT
      end}.
Admitted.
