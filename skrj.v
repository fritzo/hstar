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
  | AP : term -> term -> term.

Definition RAND x y := AP(AP R x)y.
Definition JOIN x y := AP(AP J x)y.

Hint Unfold RAND.
Hint Unfold JOIN.

Inductive red : term -> term -> Prop :=
  | red_refl: forall x, red x x
  | red_top: forall x, red TOP x
  | red_bot: forall x, red x BOT
  | red_s: forall x y z, red (AP(AP(AP S x)y)z) (AP(AP x z)(AP y z))
  | red_k: forall x y, red (AP(AP K x)y) x
  | red_rand: forall x y z, red (AP(RAND x y)z) (RAND(AP x z)(AP y z))
  | red_join: forall x y z, red (AP(JOIN x y)z) (JOIN(AP x z)(AP y z))
  | red_ap: forall x x' y y', red x x' -> red y y' -> red (AP x y) (AP x' y').


Lemma red_top_k_top : red TOP (AP K TOP).
Proof.
  apply red_top.
Qed.

Lemma top_consume : forall x, red (AP TOP x) TOP.
Proof.
  intros.
  (* TODO *)
Admitted.

Inductive prob : term -> Prop :=
  | prob_bot: prob BOT
  | prob_top: prob TOP
  | prob_rand: forall p q, prob p -> prob q -> prob (RAND p q).

Inductive approx : term -> term -> Prop :=
  | approx_rand_idem: forall x, approx x (RAND x x)
  | approx_rand_sym: forall x y, approx (RAND x y) (RAND y x)
  | approx_rand_sym_sym: forall w x y z,
    approx (RAND(RAND w x)(RAND y z)) (RAND(RAND y x)(RAND w z))
  | approx_join_1: forall x y, approx (JOIN x y) x
  | approx_join_2: forall x y, approx (JOIN x y) y.

Definition conv x p : Prop := exists y, red x y /\ approx y p.

Definition less x y := forall f p,
  conv (AP f x) p -> conv (AP f y) p.

Lemma less_refl : forall x, less x x.
Proof.
  intros.
  unfold less.
  intros.
  assumption.
Qed.

Lemma less_trans:
  forall x y z, less x y -> less y z -> less x z.
Proof.
  intros.
  unfold less.
  intros.
  auto.
Qed.

Lemma less_j_r:
  forall x y z, less (RAND (JOIN x y) z) (JOIN(RAND x z)(RAND y z)).
Proof.
  unfold less; unfold conv; intros.
  (* TODO *)

  split.
  destruct H.
  induction H.
  
  inversion H.
  injection. (* FIXME *)
  destruct H.
  inversion H.
  apply conv_r.
  assumption.
  auto.
  case .
Qed.

`Lemma equiv_join_idem: forall x, equiv x (JOIN x x).
Lemma equiv_join_sym: forall x y, equiv (JOIN x y) (JOIN y x). 
Lemma equiv_join_assoc: forall x y z,
  equiv (JOIN(JOIN x y)z) (JOIN x(JOIN y z)).
Lemma equiv_join_bot: forall x, equiv (JOIN BOT x) x.
Lemma equiv_join_top: forall x, equiv (JOIN TOP x) TOP.
Lemma equiv_join_ap: forall x y z,
  equiv (AP(JOIN x y)z) (JOIN(AP x z)(AP y z)).

Definition excluded_middle :=
  forall p : Prop, p \/ ~p.

Theorem less_is_hp_complete:
  excluded_middle ->
  forall x y, less x y \/ (less x y -> less BOT TOP).
Proof.
  (* TODO *)


(* Convenience combinators *)



