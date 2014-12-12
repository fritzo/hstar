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
  | red_trans: forall x y z, red x y -> red y z -> red x z
  | red_top: forall x, red TOP x
  | red_bot: forall x, red x BOT
  | red_s: forall x y z, red (AP(AP(AP S x)y)z) (AP(AP x z)(AP y z))
  | red_k: forall x y, red (AP(AP K x)y) x
  | red_rand: forall x y z, red (AP(RAND x y)z) (RAND(AP x z)(AP y z))
  | red_join: forall x y z, red (AP(JOIN x y)z) (JOIN(AP x z)(AP y z))
  | red_ap_1: forall x x' y, red x x' -> red (AP x y) (AP x' y)
  | red_ap_2: forall x y y', red y y' -> red (AP x y) (AP x y')
.

Inductive beta : term -> term -> Prop :=
  | beta_s: forall x y z, beta (AP(AP(AP S x)y)z) (AP(AP x z)(AP y z))
  | beta_k: forall x y, beta (AP(AP K x)y) x
  | beta_rand: forall x y z, beta (AP(RAND x y)z) (RAND(AP x z)(AP y z))
  | beta_join: forall x y z, beta (AP(JOIN x y)z) (JOIN(AP x z)(AP y z))
  | beta_ap_1: forall x x' y, beta x x' -> beta (AP x y) (AP x' y)
  | beta_ap_2: forall x y y', beta y y' -> beta (AP x y) (AP x y')
.

Inductive rho : term -> term -> Prop :=
  | rho_rand_idem: forall x, rho x (RAND x x)
  | rho_rand_sym: forall x y, rho (RAND x y) (RAND y x)
  | rho_rand_sym_sym: forall w x y z,
    rho (RAND(RAND w x)(RAND y z)) (RAND(RAND y x)(RAND w z))
.

Inductive lambda : term -> term -> Prop :=
  | lambda_top: forall x, lambda TOP x
  | lambda_bot: forall x, lambda x BOT
  | lambda_join_1: forall x y, lambda (JOIN x y) x
  | lambda_join_2: forall x y, lambda (JOIN x y) y
.

Inductive star (r : term -> term -> Prop) : term -> term -> Prop :=
  | star_refl: forall x, star r x x
  | star_trans: forall x y z, star r x y -> r y z -> star r x z
  | star_ap_1: forall x x' y, star r x x' -> star r (AP x y) (AP x' y)
  | star_ap_2: forall x y y', star r y y' -> star r (AP x y) (AP x y')
.

Inductive red' : term -> term -> Prop :=
  | red'_constructor: forall w x y z,
    star beta w x -> star rho x y -> star lambda y z -> red' w z.

Hint Constructors red.

Lemma top_consume : forall x, red (AP TOP x) TOP.
Proof.
  intros; apply red_trans with (y := AP(AP K TOP)x); eauto.
Qed.

Hint Resolve top_consume.

Inductive prob : term -> Prop :=
  | prob_bot: prob BOT
  | prob_top: prob TOP
  | prob_rand: forall p q, prob p -> prob q -> prob (RAND p q).
Hint Constructors prob.

Inductive nz_prob : term -> Prop :=
  | nz_prob_top: nz_prob TOP
  | nz_prob_rand_1: forall p q, nz_prob p -> prob q -> nz_prob (RAND p q)
  | nz_prob_rand_2: forall p q, prob p -> nz_prob q -> nz_prob (RAND p q).
Hint Constructors nz_prob.

Lemma nz_prob_prob : forall p, nz_prob p -> prob p.
Proof.
  intros.
  induction H.
  auto.
  (* TODO *)
Admitted.

Inductive approx : term -> term -> Prop :=
  | approx_rand_idem: forall x, approx x (RAND x x)
  | approx_rand_sym: forall x y, approx (RAND x y) (RAND y x)
  | approx_rand_sym_sym: forall w x y z,
    approx (RAND(RAND w x)(RAND y z)) (RAND(RAND y x)(RAND w z))
  | approx_join_1: forall x y, approx (JOIN x y) x
  | approx_join_2: forall x y, approx (JOIN x y) y.

Definition conv x p : Prop := red x p /\ prob p.
Hint Unfold conv.

Definition less x y := forall f p, conv (AP f x) p -> conv (AP f y) p.
Notation "x [= y" := (less x y) (at level 70).
Hint Unfold less.

Lemma less_refl : forall x, x [= x.
Proof. auto. Qed.

Lemma less_trans: forall x y z, x [= y -> y [= z -> x [= z.
Proof. auto. Qed.

Lemma less_j_r:
  forall x y z, RAND (JOIN x y) z [= JOIN(RAND x z)(RAND y z).
Proof.
  unfold less; unfold conv; intros.
 
  destruct H; split.
  

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

Lemma equiv_join_idem: forall x, equiv x (JOIN x x).
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


(* Interesting results *)

(* Theorem: for each exact p, Von Neumann's debiasing algorithm maps p to R. *)
(* Question: how to define exactness,
   ie the property of an R term being J-free? *)
