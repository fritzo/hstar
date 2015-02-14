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

Definition term_conv {Var : Set} : Term Var -> Prop. Admitted.
Definition term_le {Var : Set} : relation (Term Var). Admitted.
Definition term_eq {Var : Set} : relation (Term Var). Admitted.
Notation "x == y" := (term_eq x y)%term : term_scope.
Notation "x [= y" := (term_le x y)%term : term_scope.
Notation "x :: a" := (term_app a x == x)%term : term_scope.

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

Inductive Normal_ {Var : Set} : Set :=
  | Normal_top : Normal_
  | Normal_bot : Normal_
  | Normal_join : Normal_ -> Normal_ -> Normal_
  | Normal_rand : Normal_ -> Normal_ -> Normal_
  | Normal_app : Inert_ -> Normal_ -> Normal_
  | Normal_lambda : @Normal_ (option Var) -> Normal_
  | Normal_var : Var -> Normal_
with Inert_ {Var : Set} : Set :=
  | Inert_var : Var -> Inert_
  | Inert_app : Inert_ -> Normal_ -> Inert_.
Hint Constructors Normal_ Inert_.
Definition Normal (Var : Set) := @Normal_ Var.
Definition Inert (Var : Set) := @Inert_ Var.

(* This does not work
Fixpoint force_normal {Var : Set} (t : Term Var) : Normal Var :=
  match t with
  | TOP => Normal_top
  | BOT => Normal_bot
  | x || y => Normal_join (force_normal x) (force_normal y)
  | x (+) y => Normal_rand (force_normal x) (force_normal y)
  | x * y =>
      match force_inert x with
      | Inert_bot => Normal_bot
      | x' => Normal_app x' (force_normal y)
      end
  | LAMBDA x => Normal_lambda (force_normal x)
  | VAR v => Normal_var v
  end
with force_inert {Var : Set} (t : Term Var) {struct t} : Inert Var :=
  match t with
  | x * y => Inert_app (force_inert x) (force_normal y)
  | VAR v => Inert_var v
  | _ => false
  end.
*)

Fixpoint force_normal {Var : Set} (t : Term Var) : Normal Var.
Admitted.
Fixpoint forget_normal {Var : Set} (n : Normal Var) : Term Var.
Admitted.

Lemma force_forget_normal (Var : Set) (n : Normal Var) :
  force_normal (forget_normal n) = n.
Admitted.

Lemma forget_force_normal (Var : Set) (t : Term Var) :
  forget_normal (force_normal t) [= t.
Admitted.

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
  | x1 * x2 => normal_conv x1
  | term_lambda x => normal_conv x
  | term_var v => true
  end.

Lemma normal_conv_correct (Var : Set) (x : Term Var) :
  if normal_conv x then term_conv x else ~ term_conv x.
Proof.
  induction x; simpl; auto.
Admitted.

(* These version has better style, but how to implement it? *)

Definition normal_conv' {Var : Set} (x : Term Var) :
  normal x -> {term_conv x} + {~ term_conv x}.
Proof.
  intro Hn.
  set (H := normal_conv_correct Var x).
  case_eq (normal_conv x); intro Hc; rewrite Hc in H; simpl in H;
  [ apply left | apply right]; auto.
Defined.

Definition try_decide_conv {Var : Set} (x : Term Var) :
  {term_conv x} + {~ term_conv x} + {~normal x}.
Proof.
  case_eq (is_normal x); intro Hn.
  - apply normal_is_normal in Hn.
    apply inleft; apply normal_conv'; auto.
  - assert (~ is_normal x = true) as Hn'.
      rewrite Hn; auto.
    assert (~normal x) as Hc'.
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

Fixpoint normal_is_le' {Var : Set} (x y : Term Var) :
  normal x -> normal y -> {x [= y} + {~ x [= y}.
Admitted.

Lemma normal_is_le_correct (Var : Set) (x y : Term Var) :
  normal x -> normal y ->
  if normal_is_le x y then x [= y else ~ x [= y.
Admitted.

Definition normal_le {Var : Set} : relation (Term Var) :=
  fun x y => normal_is_le x y = true.

Fixpoint try_decide_le (x y : ClosedTerm) :
  {x [= y} + {~ x [= y} + {~normal x \/ ~normal y}.
Admitted.

(** ** Theorems about bohm trees and order *)

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

Theorem Bohms_theorem (x y : ClosedTerm) :
  normal x -> normal y -> ~ x [= y ->
  exists c, TOP [= c * x /\ c * y [= BOT.
Proof.
  (* TODO use the Bohm-out method *)
Admitted.

(** Constructively, we can decide order among normal forms
    and discover a witness (even a normal witness) of non-ordering. *)

Fixpoint normal_le_witness (x y : ClosedTerm) :
  normal x -> normal y ->
  {c | normal c /\ TOP [= c * x /\ c * y [= BOT} + {x [= y}.
Admitted.

Fixpoint try_decide_le_witness (x y : ClosedTerm) :
  {c | TOP [= c * x /\ c * y [= BOT /\ normal c} +
  {x [= y} +
  {~normal x \/ ~normal y}.
Admitted.

(* Extraction *)
(* begin hide *)

Extraction Language Ocaml.
Extraction "BohmTrees.ml" is_normal.

Extraction Language Haskell.
Extraction "BohmTrees.hs" is_normal.

(* end hide *)
