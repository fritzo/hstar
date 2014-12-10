Inductive term : Set :=
  | S : term
  | K : term
  | R : term
  | J : term
  | BOT : term
  | TOP : term
  | AP : term -> term -> term.

Definition JOIN x y := AP(AP J x)y.
Definition RAND x y := AP(AP R x)y.

Inductive red : term -> term -> Prop :=
  | red_s: forall x y z,
    red (AP(AP(AP S x)y)z) (AP(AP x z)(AP y z))
  | red_k: forall x y, red (AP(AP K x)y) x
  | red_r_idem: forall x, red x (RAND x x)
  | red_r_sym: forall x y, red (RAND x y) (RAND y x)
  | red_r_sym_sym: forall w x y z,
    red (RAND(RAND w x)(RAND y z))
        (RAND(RAND y x)(RAND w z))
  | red_r_ap: forall x y z,
    red (AP(RAND x y)z) (RAND(AP x z)(AP y z))
  | red_j_1: forall x y, red (JOIN x y) x
  | red_j_2: forall x y, red (JOIN x y) y
  | red_top: forall x, red TOP x
  | red_bot: forall x, red x BOT
  | red_ap_1: forall x x' y,
    red x x' -> red (AP x y) (AP x' y)
  | red_ap_2: forall x y y',
    red y y' -> red (AP x y) (AP x y').

(* conv x p
   means x converges with probability at least p
   where p is a representation of a dyadic rational *)
Inductive conv : term -> term -> Prop :=
  | conv_bot: conv BOT BOT
  | conv_top: conv TOP TOP
  | conv_r: forall x x' p p',
    conv x p -> conv x' p' -> conv (RAND x x') (RAND p p')
  | conv_red: forall x y p, red x y -> conv y p -> conv x p.

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

Definition equiv x y := less x y /\ less y x.

Lemma less_j_r:
  forall x y z, equiv (RAND (JOIN x y) z)
                      (JOIN(RAND x z)(RAND y z)).
Proof.
  intros; split.
  unfold less.
  intros.
  inversion H.
  injection.
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

