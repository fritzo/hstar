Require Import Coq.Setoids.Setoid.  (* for rewrite *)
Require Import Coq.Program.Equality.  (* for dependent induction *)

Inductive code : Set :=
  | AP : code -> code -> code
  | TOP : code
  | BOT : code
  | K : code
  | S : code.

Infix "*" := AP.

Inductive probe : code -> code -> Prop :=
  | probe_refl x : probe x x
  | probe_trans x y z : probe x y -> probe y z -> probe x z
  | probe_top x y : probe x y -> probe x (y * TOP).

Inductive beta : code -> code -> Prop :=
  | beta_refl x : beta x x
  (* this makes it difficult to prove the [head_beat_bot] lemma below
  | beta_sym x y : beta y x -> beta x y
  *)
  | beta_trans x y z : beta x y -> beta y z -> beta x z
  | beta_ap_left x x' y : beta x x' -> beta (x * y) (x' * y)
  | beta_ap_right x y y' : beta y y' -> beta (x * y) (x * y')
  | beta_k x y : beta (K * x * y) x
  | beta_s x y z : beta (S * x * y * z) (x * z * (y * z)).

Inductive test : code -> code -> Prop :=
  | test_refl x : test x x
  | test_trans x y z : test x y -> test y z -> test x z
  | test_ap_left x x' y : test x x' -> test (x * y) (x' * y)
  | test_ap_right x y y' : test y y' -> test (x * y) (x * y')
  | test_top x : test (TOP * x) TOP
  | test_bot x : test x BOT.

Definition conv (x : code) : Prop :=
  exists y z, probe x y /\ beta y z /\ test z TOP.

(* -------------------------------------------------------------------------- *)
(* head function *)

Fixpoint head (x : code) : code :=
  match x with
  | y * z => head y
  | _ => x
  end.

Lemma head_probe x y : probe x y -> head x = head y.
Proof.
  intro H; induction H; auto.
  transitivity (head y); auto.
Qed.

Lemma head_beta_bot x y : beta x y -> head x = BOT -> head y = BOT.
Proof.
  intros Ht; induction Ht; auto; compute; congruence.
Qed.

Lemma head_test_bot x y : test x y -> head x = BOT -> head y = BOT.
Proof.
  intros Ht; induction Ht; auto.
Qed.

Lemma not_conv_head_bot x : head x = BOT -> ~ conv x.
Proof.
  intros H [y [z [xy [yz zt]]]].
  apply head_probe in xy; auto; rewrite H in xy.
  apply head_beta_bot in yz; auto.
  apply head_test_bot in zt; auto.
  compute in zt.
  congruence.
Qed.

Lemma not_conv_bot : ~conv BOT.
Proof.
  apply not_conv_head_bot; compute; auto.
Qed.
Print Assumptions not_conv_bot.

(* -------------------------------------------------------------------------- *)
(* heads relation *)

Inductive heads : code -> code -> Prop :=
  | heads_refl x : heads x x
  | heads_ap h x y : heads h x -> heads h (x * y).
Hint Constructors heads.

Lemma heads_probe h x y : probe x y -> heads h x -> heads h y.
Proof.
  intro H; induction H; auto.
Qed.

Lemma heads_beta_bot x y : beta x y -> heads BOT x -> heads BOT y.
Proof.
  intros Ht; induction Ht; auto; intro Hh; inversion Hh; auto.
    inversion H1; auto.
    inversion H5; auto.
  inversion H1; auto.
  inversion H5; auto.
  inversion H9; auto.
Qed.

Lemma heads_test_bot x y : test x y -> heads BOT x -> heads BOT y.
Proof.
  intros Ht; induction Ht; auto; intro Hh; inversion Hh; auto.
Qed.

Lemma not_conv_heads_bot x : heads BOT x -> ~ conv x.
Proof.
  intros H [y [z [xy [yz zt]]]].
  apply (heads_probe _ _ y) in H; auto.
  apply (heads_beta_bot _ z) in H; auto.
  apply (heads_test_bot _ TOP) in H; auto.
  inversion H; auto.
Qed.

Lemma not_conv_bot' : ~conv BOT.
Proof.
  apply not_conv_heads_bot; auto.
Qed.
