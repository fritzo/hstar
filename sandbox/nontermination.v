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

Hint Constructors probe.
Hint Constructors beta.
Hint Constructors test.

Definition conv (x : code) : Prop :=
  exists y z, probe x y /\ beta y z /\ test z TOP.

Lemma beta_bot_bot : forall x, beta BOT x -> BOT = x.
Proof.
  intros x H.
  dependent induction H; auto.
Qed.

Lemma beta_top_top : forall x, beta TOP x -> TOP = x.
Proof.
  intros x H.
  dependent induction H; auto.
Qed.

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

Fixpoint probe' (n : nat) (x : code) :=
  match n with
  | 0 => x
  | Datatypes.S n' => probe' n' x * TOP
  end.

Lemma probe_add m n x : probe' (m + n) x = probe' m (probe' n x).
Proof.
  revert x; induction m; induction n; intros; simpl; f_equal; auto.
    assert (m + 0 = m) as eq; auto; rewrite eq.
    auto.
  rewrite IHm; simpl; auto.
Qed.

Lemma probe_probe' x y : probe x y -> exists n, y = probe' n x.
Proof.
  intro H; induction H as [x | x z y xz [m Hm] zy [n Hn] | x y xy [n Hn] ].
  - exists 0; auto.
  - exists (n + m); rewrite probe_add; rewrite <- Hm; auto.
  - exists (Datatypes.S n); simpl; f_equal; auto.
Qed.

Lemma probe'_probe n x : probe x (probe' n x).
Proof.
  revert x; induction n; simpl; auto.
Qed.

Lemma head_probe' n x : head (probe' n x) = head x.
Proof.
  symmetry; apply head_probe; apply probe'_probe.
Qed.

Lemma probe'_beta_bot n x : beta (probe' n BOT) x -> probe' n BOT = x.
Proof.
  revert x; induction n; simpl; intros; subst.
    auto using beta_bot_bot.
  dependent induction H.
  - auto.
  - apply IHbeta2; auto; symmetry; auto.
  - f_equal; auto.
  - f_equal; auto using beta_top_top.
  - assert (head (probe' n BOT) = BOT).
      transitivity (head BOT); [apply head_probe' | auto].
    assert (head (probe' n BOT) = K).
      rewrite <- x; simpl; auto.
    congruence.
  - assert (head (probe' n BOT) = BOT).
      transitivity (head BOT); [apply head_probe' | auto].
    assert (head (probe' n BOT) = S).
      rewrite <- x; simpl; auto.
    congruence.
Qed.

Lemma probe_beta_bot x y : probe BOT x -> beta x y -> x = y.
Proof.
  intro Hp; apply probe_probe' in Hp as [n eq]; subst.
  apply probe'_beta_bot.
Qed.

Lemma head_probe_bot x y : probe x y -> head x = BOT -> head y = BOT.
Proof.
  intros Ht; induction Ht; auto.
Qed.

Lemma head_beta_bot x y : beta x y -> head x = BOT -> head y = BOT.
Proof.
  intros Ht; induction Ht; auto; compute; congruence.
Qed.

Lemma head_test_bot x y : test x y -> head x = BOT -> head y = BOT.
Proof.
  intros Ht; induction Ht; auto; compute; congruence.
Qed.

Lemma not_conv_head_bot x : head x = BOT -> ~ conv x.
Proof.
  intros H [y [z [xy [yz zt]]]].
  apply head_probe_bot in xy; auto.
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
