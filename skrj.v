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
  | red_refl: forall x, red x x
  | red_trans: forall x y z, red x y -> red y z -> red x z
  | red_top: forall x, red TOP x
  | red_bot: forall x, red x BOT
  | red_s: forall x y z, red (S*x*y*z) ((x*z)*(y*z))
  | red_k: forall x y, red (K*x*y) x
  | red_r: forall x y z, red (R*x*y*z) (R*(x*z)*(y*z))
  | red_j: forall x y z, red (J*x*y*z) (J*(x*z)*(y*z))
  | red_ap_1: forall x x' y, red x x' -> red (x*y) (x'*y)
  | red_ap_2: forall x y y', red y y' -> red (x*y) (x*y')
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
  | beta_s: forall x y z, beta (S*x*y*z) ((x*z)*(y*z))
  | beta_k: forall x y, beta (K*x*y) x
  | beta_r: forall x y z, beta (R*x*y*z) (R*(x*z)*(y*z))
  | beta_j: forall x y z, beta (J*x*y*z) (J*(x*z)*(y*z))
  | beta_ap_1: forall x x' y, beta x x' -> beta (x*y) (x'*y)
  | beta_ap_2: forall x y y', beta y y' -> beta (x*y) (x*y')
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
  | lambda_top: forall x, lambda TOP x
  | lambda_bot: forall x, lambda x BOT
  | lambda_join_1: forall x y, lambda (JOIN x y) x
  | lambda_join_2: forall x y, lambda (JOIN x y) y
.

(* dyadic rational probabilities *)

Inductive rho : term -> term -> Prop :=
  | rho_rand_idem: forall x, rho x (RAND x x)
  | rho_rand_sym: forall x y, rho (RAND x y) (RAND y x)
  | rho_rand_sym_sym: forall w x y z,
    rho (RAND(RAND w x)(RAND y z)) (RAND(RAND y x)(RAND w z))
.

Inductive star (r : term -> term -> Prop) : term -> term -> Prop :=
  | star_refl: forall x, star r x x
  | star_trans: forall x y z, star r x y -> r y z -> star r x z
  | star_ap_1: forall x x' y, star r x x' -> star r (x*y) (x'*y)
  | star_ap_2: forall x y y', star r y y' -> star r (x*y) (x*y')
.

Inductive red' : term -> term -> Prop :=
  | red'_constructor: forall w x y z,
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

Lemma red_j_r: forall x y z p,
  red' (RAND(JOIN x y)z) p -> red' (JOIN(RAND x y)(RAND x z)) p.
Proof.
  intros.
  destruct H.
  (* TODO *)
Admitted.

Definition equiv x y := less x y /\ less y x.

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

Definition excluded_middle :=
  forall p : Prop, p \/ ~p.

Theorem less_is_hp_complete:
  excluded_middle ->
  forall x y, less x y \/ (less x y -> less BOT TOP).
Proof.
  (* TODO *)
Admitted.


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

Definition C := TOP. (* FIXME *)
Definition PAIR x y := (C*I*x) o (C*I*y).

Theorem a_definable: {a | forall s r, less (r o s) I -> less (PAIR s r) a}.
Proof.
  (* TODO *)
Admitted.

Definition A : term := proj1_sig a_definable.

(* abstraction notation *)
Inductive open_term :=
  | var : nat -> open_term
  | open_ap : open_term -> open_term -> open_term
  | open_from_closed :  term -> open_term.

Fixedpoint closed_from_open (u : open_term) : term :=
  match u with
  | var n => TOP
  | open_ap x y => (closed_from_open x) * (closed_from_open y)
  | open_from_closed x => x
  end.

Fixedpoint lambda (n : nat) (u : open_term) :=
  match u with
  | var n0 =>
    open_from_closed (if n0 = n then I else K)
  | open_ap x y =>
    open_ap (open_ap (open_from_closed S) (lambda n x) (lambda n y))
  | open_from_closed x => open_from_closed x
  end.

Definition semi := A * (closed_from_open (abs fun x => x --> x)).

Theorem closure_i: A 
