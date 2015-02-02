(** * Reasoning about nontermination *)

Require Export Combinators.
Open Scope code_scope.

Lemma sub_top_le (Var : Set) (x : Code Var) (f : Var -> Code Empty_set) :
  x @ f [= x @ sub_top.
Proof.
  induction x; simpl; intros; auto.
  freeze code_le in compute.
  auto.
Qed.

Lemma not_conv_eq_bot (Var : Set) (x : Code Var) :
  ~ conv (x @ sub_top) -> x == BOT.
Proof.
  intro Hd; split; auto.
  code_le_weaken; intros c f Hc.
  rewrite sub_top_le in Hc.
  apply conv_apply in Hc.
  contradiction.
Qed.

Fixpoint probed {Var : Set} (n : nat) (x : Code Var) : Code Var :=
  match n with
  | 0%nat => x
  | (Succ n')%nat => (probed n' x) * code_top
  end.

Lemma probe_bot_top (Var : Set) : forall n, probed n (@code_bot Var) <> TOP.
Proof.
  intros n; induction n; compute; fold (@probed Var); discriminate.
Qed.

Lemma ap_top_div (Var : Set) (x : Code Var) : div * (x * TOP) == div * x.
Proof.
  split.
    rewrite (@code_eq_div' _ x); auto.
Admitted.

Lemma div_ap_top (Var : Set) (x : Code Var) : div * x * TOP == div * x.
Proof.
  split.
    rewrite code_eq_div at 2. rewrite pi_j_right; auto.
  intros Var' c f [y [xy yt]].
Admitted.

Lemma div_repeat_top (Var : Set) (x : Code Var) (n : nat) :
  (div * x) ** TOP ^^ n == div * x.
Proof.
  induction n; simpl; auto.
  rewrite div_ap_top; auto.
Qed.

Lemma repeat_top_div (Var : Set) (x : Code Var) (n : nat) :
  div * (x ** TOP ^^ n) == div * x.
Proof.
  induction n; simpl; auto.
  rewrite code_repeat_commute_1.
  rewrite ap_top_div; auto.
Qed.

Lemma div_probe_bot (Var : Set) :
  forall n : nat, ~ conv (probed n (@code_bot Var)).
Proof.
  intros n; apply not_conv_heads_bot.
  induction n; simpl; heads.
Qed.

Lemma div_bot (Var : Set) : div * BOT == (BOT : Code Var).
Proof.
  unfold div.
  (* TODO this could be proved from an asymmetric definition of beta *)
Admitted.
Hint Rewrite div_bot : code_simpl.

Section Omega.
  Context {Var : Set}.
  Let x := make_var Var 0.
  Definition Omega := Eval compute in close_var ((\x, x * x) * (\x, x * x)).
End Omega.

Lemma code_le_omega_bot (Var : Set) : (@Omega Var) [= BOT.
Proof.
  unfold Omega, code_le; intros Var' c f Ha.
  induction Ha.
  (* TODO this could be proved from an asymmetric definition of beta *)
Admitted.

Lemma code_eq_omega_bot (Var : Set) : (@Omega Var) == BOT.
Proof.
  split ; (apply code_le_omega_bot || auto).
Qed.
