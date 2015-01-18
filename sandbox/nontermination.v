Require Import Coq.Program.Equality.

Inductive code : Set :=
  | AP : code -> code -> code
  | TOP : code
  | BOT : code
  | I : code
  | K : code
  | S : code.

Infix "*" := AP.

Inductive probe : code -> code -> Prop :=
  | probe_refl x : probe x x
  | probe_trans x y z : probe x y -> probe y z -> probe x z
  | probe_top x y : probe x y -> probe x (y * TOP).

Inductive beta : code -> code -> Prop :=
  | beta_refl x : beta x x
  | beta_trans x y z : beta x y -> beta y z -> beta x z
  | beta_ap_left x x' y : beta x x' -> beta (x * y) (x' * y)
  | beta_ap_right x y y' : beta y y' -> beta (x * y) (x * y')
  | beta_i x : beta (I * x) x
  | beta_k x y : beta (K * x * y) x
  | beta_s x y z : beta (S * x * y * z) (x * z * (y * z)).
Hint Constructors beta.

Inductive beta_step : code -> code -> Prop :=
  | beta_step_ap_left x x' y : beta_step x x' -> beta_step (x * y) (x' * y)
  | beta_step_ap_right x y y' : beta_step y y' -> beta_step (x * y) (x * y')
  | beta_step_i x : beta_step (I * x) x
  | beta_step_k x y : beta_step (K * x * y) x
  | beta_step_s x y z : beta_step (S * x * y * z) (x * z * (y * z)).
Hint Constructors beta_step.

Inductive test : code -> code -> Prop :=
  | test_refl x : test x x
  | test_trans x y z : test x y -> test y z -> test x z
  | test_ap_left x x' y : test x x' -> test (x * y) (x' * y)
  | test_ap_right x y y' : test y y' -> test (x * y) (x * y')
  | test_top x : test (TOP * x) TOP
  | test_bot x : test x BOT.

Definition conv (x : code) : Prop :=
  exists y z, probe x y /\ beta y z /\ test z TOP.

Lemma beta_beta_step : forall x y, beta_step x y -> beta x y.
Proof.
  intros x y H; induction H; auto.
Qed.

Lemma beta_closed (p : code -> Prop) :
  (forall x y, beta_step x y -> p x -> p y) ->
  forall x y, beta x y -> p x -> p y.
Proof.
  intros Hs x y Hb; induction Hb; auto.
Admitted.

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

Lemma not_conv_bot : ~ conv BOT.
Proof.
  apply not_conv_head_bot; compute; auto.
Qed.
Print Assumptions not_conv_bot.

(* -------------------------------------------------------------------------- *)
(* heads relation *)

Inductive heads : code -> code -> Prop :=
  | heads_refl x : heads x x
  | heads_ap h x y : heads h x -> heads h (x * y).

Ltac heads :=
  auto using heads_refl, heads_ap;
  match goal with
  | [H : heads ?x ?y |- _] => inversion_clear H; heads
  end.

Lemma heads_probe h x y : probe x y -> heads h x -> heads h y.
Proof.
  intro H; induction H; heads.
Qed.

Lemma heads_beta_bot x y : beta x y -> heads BOT x -> heads BOT y.
Proof.
  intros Ht; induction Ht; intros; heads.
Qed.

Lemma heads_test_bot x y : test x y -> heads BOT x -> heads BOT y.
Proof.
  intros Ht; induction Ht; intros; heads.
Qed.

Lemma not_conv_heads_bot x : heads BOT x -> ~ conv x.
Proof.
  intros H [y [z [xy [yz zt]]]].
  apply (heads_probe _ _ y) in H; auto.
  apply (heads_beta_bot _ z) in H; auto.
  apply (heads_test_bot _ TOP) in H; auto.
  inversion H; auto.
Qed.

Lemma not_conv_bot' : ~ conv BOT.
Proof.
  apply not_conv_heads_bot; heads.
Qed.

Definition Omega := (S * I * I) * (S * I * I).

Definition Omega_beta (x : code) :=
  x = (I * (S * I * I) * (I * (S * I * I))) \/
  x = ((S * I * I) * (I * (S * I * I))) \/
  x = (I * (S * I * I) * (S * I * I)) \/
  x = ((S * I * I) * (S * I * I))
.
Hint Unfold Omega_beta.

Definition Omega_heads (x : code) :=
  heads (I * (S * I * I) * (I * (S * I * I))) x \/
  heads ((S * I * I) * (I * (S * I * I))) x \/
  heads (I * (S * I * I) * (S * I * I)) x \/
  heads ((S * I * I) * (S * I * I)) x.

Ltac beta_step :=
  auto;
  match goal with
  | [H : beta_step ?x ?y |- _] => inversion_clear H; beta_step || idtac
  end.

Lemma beta_omega x y : beta x y -> Omega_beta x -> Omega_beta y.
Proof.
  apply beta_closed; intros.
  destruct H0 as [o1|[o2|[o3|o4]]]; subst; auto; beta_step.
  (* FIXME reduced to (I * (I * (S * I * I)) * (I * (I * (S * I * I)))) *)
Admitted.

Lemma not_conv_omega : ~ conv Omega.
Proof.
Admitted.
