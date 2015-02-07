(** * Head normal form, %B\"{o}hm% trees, and the %B\"{o}hm%-out method *)

(** This follows Jean-Jacques Lévy's formalization
    http://pauillac.inria.fr/~levy/courses/tsinghua/lambda/3-5/lecture3-5.pdf
    *)

Require Import Coq.Program.Basics.
Require Import Coq.Program.Equality.
Require Import Coq.Setoids.Setoid.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Lists.List.
Require Export InformationOrdering.
Require Export LeastFixedPoint.
Open Scope code_scope.

(** ** Normal form *)

Fixpoint try_beta_step {Var : Set} (x : Code Var) : option (Code Var) :=
  match x with
    | I * x => Some x
    | K * x * y => Some x
    | B * x * y * z => Some (x * (y * z))
    | C * x * y * z => Some (x * z * y)
    | S * x * y * z => Some (x * z * (y * z))
    | (x || y) * z => Some (x * z || y * z)
    | (x (+) y) * z => Some (x * z (+) y * z)
    | x * y =>
        match try_beta_step x with
          | Some x' => Some (x' * y)
          | None =>
              match try_beta_step y with
                | Some y' => Some (x * y')
                | None => None
              end
        end
    | _ => None
  end.

Definition is_beta_normal {Var : Set} (x : Code Var) : bool :=
  match try_beta_step x with
    | Some _ => false
    | None => true
  end.

Fixpoint is_hnf (x : Closed) : bool :=
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

(* This gross combinatory definition requires side calculations.
   Is there a more direct way to define hnf in terms of abstraction? *)

Inductive hnf : nat -> Closed -> Prop :=
  | hnf_succ n x : hnf (Succ n) x -> hnf n x
  | hnf_ap n x y : hnf (Succ n) x -> hnf n (x * y)
  | hnf_i : hnf 0 I
  | hnf_k : hnf 0 K
  | hnf_k1 x : hnf 0 x -> hnf 0 (K * x)
  | hnf_s : hnf 0 S
  | hnf_s1 n x : hnf (Succ (Succ n)) x -> hnf n (S * x)
  | hnf_s2 n x y : hnf (Succ (Succ n)) x -> hnf n (S * x * y)
  | hnf_j2 n x y : hnf n x -> hnf n y -> hnf n (J * x * y)
  | hnf_r2 n x y : hnf n x -> hnf n y -> hnf n (R * x * y)
.

(* Maybe try an abstraction-based definition
Inductive hnf' : Closed -> Prop :=
  hnf'_var v xs : hnf' (code_var v ** xs)
  hnf'_app :
*)

Lemma commute_drop_fake : K o (C * I * BOT) [= (C * I * BOT) o (K : Closed).
Proof.
  eta_expand; eta_expand; beta_simpl; monotonicity.
Qed.

Parameter Var : Set.
Let x := make_var Var 0.
Let y := make_var Var 1.
Let z := make_var Var 2.
Eval compute in close_var (\x, \x, \y, \x, \x, y * BOT).

(** The [conv_bt_witness] theorem is a simple example of the Bohm-out technique:
    we start with convergenc of an arbitrary "algebraic" term
    and construct a minimal hnf witness of convergence. *)

Lemma pi_top_bt_witness (x : Closed) :
  pi x TOP -> exists k1 k2 b, K ^ k1 * (K ^ k2 o (C * I * BOT) ^ b) [= x.
Proof.
  intro xt; apply weaken_pi in xt.
  inversion xt; eauto.
  induction H.
Admitted.

Theorem conv_bt_witness (x : Closed) :
  conv x -> exists k1 k2 b, K ^ k1 * (K ^ k2 o (C * I * BOT) ^ b) [= x.
Proof.
  intro H; rewrite conv_closed in H; destruct H as [y [xy yt]].
  apply weaken_probe in xy; apply weaken_pi in yt.
  dependent induction yt; eauto.
  - admit.
  - admit.
Qed.


Fixpoint approximate (x : Closed) : Closed :=
  if negb (is_hnf x) then BOT else
  match x with
    | x * y => approximate x * approximate y
    | _ => x
  end.

Inductive approximated_by (x : Closed) : Closed -> Prop :=
  approximated_by_intro y : pi x y -> approximated_by x (approximate y).

Theorem normal_conv (c x : Closed) :
  conv (c * x) -> exists y, approximated_by x y /\ conv (c * y).
Proof.
Admitted.

Theorem normal_interpolate (x y : Closed) :
  ~ y [= x -> exists y', approximated_by y y' /\ ~ y' [= x.
Proof.
Admitted.
