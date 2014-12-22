Require Import Equivalence.
Require Import List.

(* [BOT] and [TOP] are [S,K,J,AP]-definable,
   but specifying them simplifies convergence below *)
Inductive term : Set :=
  | TOP : term
  | BOT : term
  | S : term
  | K : term
  | R : term
  | J : term
  | AP : term -> term -> term
.

Notation "x * y" := (AP x y) (at level 40, left associativity).
Definition RAND x y := R * x * y.
Definition JOIN x y := J * x * y.
Hint Unfold RAND.
Hint Unfold JOIN.

Inductive red : term -> term -> Prop :=
  | red_refl x: red x x
  | red_trans x y z: red x y -> red y z -> red x z
  | red_top x: red TOP x
  | red_bot x: red x BOT
  | red_s x y z: red (S*x*y*z) ((x*z)*(y*z))
  | red_k x y: red (K*x*y) x
  | red_r x y z: red (R*x*y*z) (R*(x*z)*(y*z))
  | red_j x y z: red (J*x*y*z) (J*(x*z)*(y*z))
  | red_ap_1 x x' y: red x x' -> red (x*y) (x'*y)
  | red_ap_2 x y y': red y y' -> red (x*y) (x*y')
.

Fixpoint beta_step (u : term) : option term :=
  match u with
  | S*x*y*z => Some (x*z*(y*z))
  | K*x => Some x
  | R*x*y*z => Some (R*(x*z)*(y*z))
  | J*x*y*z => Some (J*(x*z)*(y*z))
  | x * y =>
    match beta_step x with
    | Some x0 => Some (x0*y)
    | None =>
      match beta_step y with
      | Some y0 => Some (x*y0)
      | None => None
      end
    end
  | _ => None
  end.

Inductive beta : term -> term -> Prop :=
  | beta_s x y z: beta (S*x*y*z) ((x*z)*(y*z))
  | beta_k x y: beta (K*x*y) x
  | beta_r x y z: beta (R*x*y*z) (R*(x*z)*(y*z))
  | beta_j x y z: beta (J*x*y*z) (J*(x*z)*(y*z))
  | beta_ap_1 x x' y: beta x x' -> beta (x*y) (x'*y)
  | beta_ap_2 x y y': beta y y' -> beta (x*y) (x*y')
.

Lemma beta_step_beta : forall x,
  match beta_step x with
  | Some y => beta x y
  | None => True
  end.
Proof.
  intros.
  (* TODO *)
Admitted.

Inductive lambda : term -> term -> Prop :=
  | lambda_top x: lambda TOP x
  | lambda_bot x: lambda x BOT
  | lambda_join_1 x y: lambda (JOIN x y) x
  | lambda_join_2 x y: lambda (JOIN x y) y
.

(* dyadic rational probabilities *)

Inductive rho : term -> term -> Prop :=
  | rho_rand_idem x: rho x (RAND x x)
  | rho_rand_sym x y: rho (RAND x y) (RAND y x)
  | rho_rand_sym_sym w x y z:
    rho (RAND(RAND w x)(RAND y z)) (RAND(RAND y x)(RAND w z))
.

Inductive star (r : term -> term -> Prop) : term -> term -> Prop :=
  | star_refl x: star r x x
  | star_trans x y z: star r x y -> r y z -> star r x z
  | star_ap_1 x x' y: star r x x' -> star r (x*y) (x'*y)
  | star_ap_2 x y y': star r y y' -> star r (x*y) (x*y')
.

Inductive red' : term -> term -> Prop :=
  | red'_constructor w x y z:
    star beta w x -> star rho x y -> star lambda y z -> red' w z.

Hint Constructors red.

Lemma top_consume : forall x, red (TOP*x) TOP.
Proof.
  intros; apply red_trans with (y := K*TOP*x); eauto.
Qed.

Hint Resolve top_consume.

Inductive prob : term -> Prop :=
  | prob_bot: prob BOT
  | prob_top: prob TOP
  | prob_rand p q: prob p -> prob q -> prob (RAND p q).
Hint Constructors prob.

Inductive nz_prob : term -> Prop :=
  | nz_prob_top: nz_prob TOP
  | nz_prob_rand_1 p q: nz_prob p -> prob q -> nz_prob (RAND p q)
  | nz_prob_rand_2 p q: prob p -> nz_prob q -> nz_prob (RAND p q).
Hint Constructors nz_prob.

Lemma nz_prob_prob : forall p, nz_prob p -> prob p.
Proof.
  intros.
  induction H.
  auto.
  (* TODO *)
Admitted.

Inductive approx : term -> term -> Prop :=
  | approx_rand_idem x: approx x (RAND x x)
  | approx_rand_sym x y: approx (RAND x y) (RAND y x)
  | approx_rand_sym_sym w x y z:
    approx (RAND(RAND w x)(RAND y z)) (RAND(RAND y x)(RAND w z))
  | approx_join_1 x y: approx (JOIN x y) x
  | approx_join_2 x y: approx (JOIN x y) y.

Definition conv x p : Prop := red x p /\ prob p.
Hint Unfold conv.

Definition less x y := forall f p, conv (AP f x) p -> conv (AP f y) p.
Notation "x [= y" := (less x y) (at level 70, no associativity).
Hint Unfold less.

Definition equiv x y := less x y /\ less y x.
Notation "x [=] y" := (equiv x y) (at level 70, no associativity).
Hint Unfold equiv.

Lemma less_refl : forall x, x [= x.
Proof. auto. Qed.
Hint Resolve less_refl.

Lemma less_trans: forall x y z, x [= y -> y [= z -> x [= z.
Proof. auto. Qed.

Lemma less_antisym : forall x y, x [= y -> y [= x -> x [=] y.
Proof. auto. Qed.
Hint Resolve less_antisym.

Lemma equiv_refl : forall x, x [=] x.
Proof. auto. Qed.
Hint Resolve equiv_refl.

Lemma equiv_sym : forall x y, x [=] y -> y [=] x.
Proof. firstorder. Qed.
Hint Resolve equiv_sym.

Lemma equiv_trans : forall x y z, x [=] y -> y [=] z -> x [=] z.
Proof.
  intros x y z H0 H1. unfold equiv. destruct H0. destruct H1. split; auto.
Qed.

(* Instance Term_Equivalence : Equivalence equiv *)
Instance less_preorder : PreOrder less.
Proof.
  simpl_relation.
Defined.

Instance equiv_Equivalence : Equivalence (A := term) equiv := {}.
Proof.
  simpl_relation.
  simpl_relation. firstorder.
  simpl_relation. apply (equiv_trans x y z); auto.
Defined.

Instance term_PartialOrder : PartialOrder (A := term) equiv less.
Proof.
  simpl_relation.
Defined.

Lemma red_j_r: forall x y z p,
  red' (RAND(JOIN x y)z) p -> red' (JOIN(RAND x y)(RAND x z)) p.
Proof.
  intros.
  destruct H.
  (* TODO *)
Admitted.

Lemma less_j_r:
  forall x y z, RAND (JOIN x y) z [= JOIN(RAND x z)(RAND y z).
Proof.
  unfold less; unfold conv; intros.
 
  destruct H; split.
  (* TODO *)
Admitted.

Lemma equiv_join_idem: forall x, equiv x (JOIN x x).
Admitted.
Lemma equiv_join_sym: forall x y, equiv (JOIN x y) (JOIN y x). 
Admitted.
Lemma equiv_join_assoc: forall x y z,
  equiv (JOIN(JOIN x y)z) (JOIN x(JOIN y z)).
Admitted.
Lemma equiv_join_bot: forall x, equiv (JOIN BOT x) x.
Admitted.
Lemma equiv_join_top: forall x, equiv (JOIN TOP x) TOP.
Admitted.
Lemma equiv_join_ap: forall x y z,
  equiv (AP(JOIN x y)z) (JOIN(AP x z)(AP y z)).
Admitted.

Definition excluded_middle := forall p : Prop, p \/ ~p.

Theorem less_is_hp_complete:
  excluded_middle ->
  forall x y, less x y \/ (less x y -> less TOP BOT).
Proof.
  (* TODO *)
Admitted.
(* Question: Can this be stated intuitionistically? *)

(* Convenience combinators *)

Definition I := S * K * K.
Definition COMP x y := S * (K * x) * y.
Notation "x 'o' y" := (COMP x y) (at level 30, right associativity).
Hint Unfold COMP.
Hint Unfold I.

Lemma red_i: forall x, red (I * x) x.
Proof.
  intros.
  unfold I.
  apply red_trans with (y := K * x * (K * x)); eauto.
Qed.

Definition B := S * (K * S) * K.
Hint Unfold B.

Lemma red_b: forall x y z, B*x*y*z = x*(y*z).
Proof.
  intros.
  unfold B.
  (* TODO *)
Admitted.

(* Interesting results *)

(* Theorem: for each exact p, Von Neumann's debiasing algorithm maps p to R. *)
(* Question: how to define exactness,
   ie the property of an R term being J-free? *)

(* definable types *)

Definition V := TOP (* TODO *).
Definition fixes a x := less (V * a * x) x.

Definition C := TOP. (* FIXME *)
Definition PAIR x y := (C*I*x) o (C*I*y).

Theorem a_definable: {a | forall s r, less (r o s) I <-> less (PAIR s r) a}.
Proof.
  (* TODO *)
Admitted.

Definition A : term := proj1_sig a_definable.

(* abstraction notation *)

Inductive open_term :=
  | VAR : nat -> open_term
  | open_ap : open_term -> open_term -> open_term
  | open : term -> open_term.

Notation "[ x ]" := (open x).
Notation "x [*] y" := (open_ap x y) (at level 40, left associativity).

Fixpoint close (u : open_term) : term :=
  match u with
  | VAR n => TOP
  | open_ap x y => (close x) * (close y)
  | open x => x
  end.

Require Import EqNat.

Fixpoint LAMBDA (n : nat) (u : open_term) :=
  match u with
  | VAR n0 => open (if beq_nat n0 n then I else K)
  | open_ap x y => open_ap (open_ap (open S) (LAMBDA n x)) (LAMBDA n y)
  | open x => open x
  end.

Definition semi := A * close (LAMBDA 0 (LAMBDA 1 (
  [TOP] (* TODO *)
))).

Inductive Prob l u : term -> Prop :=
  | Prob_bot: Prob BOT
  | Prob_top: Prob I
  | Prob_rand p q: Prob l u p -> Prob l u q -> Prob l u (RAND p q)
  | Prob_equiv p': prob p' -> equiv p' p -> prob p
  | Prob_lim: forall (s : Set) (ps : s -> Prob l u).

Inductive semi_fixes : term -> Set :=
  | semi_fixes_i p : Prob BOT I: semi_fixes p
  | semi_fixes_top: semi_fixes TOP.

Definition inhabitants (a : term) (a_fixes : term -> Set) : Prop :=
  forall x, a_fixes x <-> fixes a x.

Theorem semi_inhabs:
  (forall x : term, semi_fixes x <-> fixes semi x)
  (f BOT /\ f I /\ f TOP) /\
  forall x, f x -> (equiv x BOT \/ equiv x I \/ equiv x TOP).
Proof.
  (* TODO *)
Admitted.

Definition 
