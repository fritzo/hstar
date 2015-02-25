Require Import Coq.Program.Basics.
Require Import Coq.Program.Equality.
Require Import Coq.Setoids.Setoid.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Logic.Decidable.
Require Import Coq.Bool.Bool.
Require Import BohmTrees.

(* for reference
Inductive Term {Vs : Set} : Set :=
  | term_top : Term
  | term_bot : Term
  | term_join : Term -> Term -> Term
  | term_rand : Term -> Term -> Term
  | term_app : Term -> Term -> Term
  | term_var : Vs -> Term
  | term_lambda : @Term (option Vs) -> Term.
Arguments Term : default implicits.
Hint Constructors Term.

Inductive normal {Vs : Set} : Term Vs -> Prop :=
  | normal_bot : normal BOT
  | normal_join x y : normal x -> normal y -> normal (x || y)
  | normal_rand x y : normal x -> normal y -> normal (x (+) y)
  | normal_app x y : inert x -> normal y -> normal (x * y)
  | normal_lambda x : @normal (option Vs) x -> normal (LAMBDA x)
  | normal_var v : normal (VAR v)
with inert {Vs : Set} : Term Vs -> Set :=
  | inert_var v : inert (VAR v)
  | inert_app x y : inert x -> normal y -> inert (x * y).
Hint Constructors normal inert.
*)

Inductive Normal {Vs : Set} : Set :=
  | Normal_bot : Normal
  | Normal_join : Normal -> Normal -> Normal
  | Normal_rand : Normal -> Normal -> Normal
  | Normal_app : Inert -> Normal -> Normal
  | Normal_lambda : @Normal (option Vs) -> Normal
  | Normal_var : Vs -> Normal
with Inert {Vs : Set} : Set :=
  | Inert_var : Vs -> Inert
  | Inert_app : Inert -> Normal -> Inert.
Hint Constructors Normal Inert.
Arguments Normal : default implicits.
Arguments Inert : default implicits.

(*
Fixpoint force_normal {Vs : Set} (t : Term Vs) : Normal Vs.  Admitted.
Fixpoint forget_normal {Vs : Set} (n : Normal Vs) : Term Vs.  Admitted.
Lemma force_forget {Vs : Set} (n : Normal Vs) :
  force_normal (forget_normal n) = n.
*)

Inductive Tp {Vs : Set} : Set :=
  | Tp_var : Vs -> Tp
  | Tp_exp : Tp -> Tp -> Tp
  | Tp_hole : Tp
  | Tp_error : Tp.
Hint Constructors Tp.
Arguments Tp : default implicits.

Definition delta (Var : Set) := forall x y : Var, {x = y} + {~ x = y}.

Definition sumbool_if {p q : Prop} {t : Type} : {p} + {q} -> t -> t -> t :=
  fun b x y =>
  match b with
  | left _ => x
  | right _ => y
  end.

(* TODO this does not specialize *)
Fixpoint unify {Vs : Set} (d : delta Vs) (a b : Tp Vs) : Tp Vs :=
  match a, b with
  | Tp_hole, c => c
  | c, Tp_hole => c
  | Tp_var v, Tp_var v' => sumbool_if (d v v') a Tp_error
  | Tp_exp a1 a2, Tp_exp b1 b2 =>
    let c1 := unify d a1 b1 in
    let c2 := unify d a2 b2 in
    match c1, c2 with
    | Tp_error, _ => Tp_error
    | _, Tp_error => Tp_error
    |_, _ => Tp_exp c1 c2
    end
  | _, _ => Tp_error
  end.

Inductive TNormal {Ts Vs : Set} : Set :=
  | TNormal_bot : Tp Ts -> TNormal
  | TNormal_join : Tp Ts -> TNormal -> TNormal -> TNormal
  | TNormal_rand : Tp Ts -> TNormal -> TNormal -> TNormal
  | TNormal_app : Tp Ts -> TInert -> TNormal -> TNormal
  | TNormal_lambda : Tp Ts -> @TNormal Ts (option Vs) -> TNormal
  | TNormal_var : Tp Ts -> Vs -> TNormal
with TInert {Ts Vs : Set} : Set :=
  | TInert_var : Tp Ts -> Vs -> TInert
  | TInert_app : Tp Ts -> TInert -> TNormal -> TInert.
Hint Constructors TNormal TInert.
Arguments TNormal : default implicits.
Arguments TInert : default implicits.

Fixpoint annotate_any {Ts Vs : Set} (n : Normal Vs) : TNormal Ts Vs :=
  match n with
  | Normal_bot => TNormal_bot Tp_hole
  | Normal_join x y => TNormal_join Tp_hole (annotate_any x) (annotate_any y)
  | Normal_rand x y => TNormal_rand Tp_hole (annotate_any x) (annotate_any y)
  | Normal_app x y => TNormal_app Tp_hole (annotate_any' x) (annotate_any y)
  | Normal_lambda x => TNormal_lambda Tp_hole (annotate_any x)
  | Normal_var v => TNormal_var Tp_hole v
  end
with annotate_any' {Ts Vs : Set} (i : Inert Vs) : TInert Ts Vs :=
  match i with
  | Inert_var v => TInert_var Tp_hole v
  | Inert_app x y => TInert_app Tp_hole (annotate_any' x) (annotate_any y)
  end.

(* TODO
Inductive inhabits {Ts Vs : Set} : Normal Vs -> Tp Ts -> Prop :=
  | inhabits_bot t : inhabits Normal_bot t
.

Inductive infers {Ts Vs : Set} : relation (TNormal Ts Vs) :=
  | infers_bot t : infers (TNormal_bot Tp_hole) (TNormal_bot t)
  | infers_join t tx x ty y :
      infers tx x
.
*)
