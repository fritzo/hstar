(** * Head normal form, %S\"{o}hm% trees, and the %S\"{o}hm%-out method *)

(** This follows Jean-Jacques Lévy's formalization
    http://pauillac.inria.fr/~levy/courses/tsinghua/lambda/3-5/lecture3-5.pdf
    *)

Require Import Coq.Program.Basics.
Require Import Coq.Setoids.Setoid.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Lists.List.
Require Export InformationOrdering.
Open Scope code_scope.

(** ** Normal form *)

Fixpoint is_hnf {Var : Set} (x : Code Var) : bool :=
  match x with
    | I => true
    | K => true
    | K * x => true
    | S => true
    | S * x => is_hnf x
    | S * x * y => is_hnf x
    | x || y => andb (is_hnf x) (is_hnf y)
    | x (+) y => andb (is_hnf x) (is_hnf y)
    | _ => false
  end.

Inductive hnf {Var : Set} : nat -> Code Var -> Prop :=
  | hnf_succ n x : hnf (Succ n) x -> hnf n x
  | hnf_var n v : hnf n (code_var v)
  | hnf_ap n x y : hnf (Succ n) x -> hnf n (x * y)
  | hnf_i : hnf 0 I
  | hnf_k : hnf 0 K
  | hnf_k1 x : hnf 0 x -> hnf 0 (K * x)
  | hnf_s : hnf 0 S
  | hnf_s1 x : hnf 2 x -> hnf 0 (S * x)
  | hnf_s2 x y : hnf 2 x -> hnf 0 (S * x * y)
  | hnf_j n x y : hnf n x -> hnf n y -> hnf n (x || y)
  | hnf_r n x y : hnf n x -> hnf n y -> hnf n (x (+) y)
.

Fixpoint approximate {Var : Set} (x : Code Var) : Code Var :=
  if negb (is_hnf x) then BOT else
  match x with
    | x * y => approximate x * approximate y
    | _ => x
  end.

Inductive approximated_by {Var : Set} (x : Code Var) : Code Var -> Prop :=
  approximated_by_intro y : pi x y -> approximated_by x (approximate y).

Theorem normal_interpolate {Var : Set} (x y : Code Var) :
  ~ y [= x -> exists y', approximated_by y y' /\ ~ y' [= x.
Proof.
Admitted.

(* OLD
Theorem hnf_conv :
  forall f x : Ob, conv (f * x) ->
  {y : Ob & y [= x & ((hnf y) * (conv (f * y)))%type}.
Proof.
  intros f x Hconv.
  inversion Hconv.
  (* TODO *)
Admitted.
*)
