(** * Reasoning about nontermination *)

Require Import Coq.Logic.Classical_Pred_Set.
Require Export Combinators.
Open Scope code_scope.

Lemma sub_top_le (Var : Set) (x : Code Var) (f : Var -> Code Empty_set) :
  x @ f [= x @ sub_top.
Proof.
  induction x; simpl; intros; auto.
  freeze code_le in compute.
  auto.
Qed.

Lemma conv_nle_bot (Var : Set) (x : Code Var) : conv x <-> ~ x [= BOT.
Proof.
  split.
  - unfold code_le; intros H Hneg.
    apply (@not_conv_bot Var).
    rewrite <- beta_i; rewrite <- (@var_monad_unit_right Var _).
    apply Hneg; code_simpl; auto.
  - rewrite code_le_weaken.
    intro H.
    apply not_all_ex_not in H; destruct H as [ys H].
    apply not_all_ex_not in H; destruct H as [f H].
    apply not_all_ex_not in H; destruct H as [H Hb]; clear Hb.
    apply conv_apply in H.
    rewrite <- conv_close; unfold close.
    simpl in x.
    revert H; apply conv_proper_le.
    apply sub_top_le.
Qed.

Lemma not_conv_eq_bot (Var : Set) (x : Code Var) : ~ conv x <-> x == BOT.
Proof.
  split.
  - intro Hd; split; auto.
    code_le_weaken; intros c f Hc.
    rewrite sub_top_le in Hc.
    apply conv_apply in Hc.
    fold (@close Var) in Hc.
    rewrite conv_close in Hc.
    contradiction.
  - intros [H H']; clear H'.
    intro Hc.
    rewrite <- beta_i in Hc; rewrite <- (@var_monad_unit_right Var _) in Hc.
    apply H in Hc.
    code_simpl in Hc.
    apply not_conv_bot in Hc; auto.
Qed.

Lemma not_conv_div_bot (Var : Set) : ~ conv (div * BOT : Code Var).
Proof.
  (* TODO enumerate pi-reachable terms, then show TOP is not reachable *)
Admitted.

Lemma div_bot (Var : Set) : div * BOT == (BOT : Code Var).
Proof.
  apply not_conv_eq_bot; apply not_conv_div_bot.
Qed.
Hint Rewrite div_bot : code_simpl.

Lemma code_eq_ap_bot (Var : Set) (x : Code Var) : BOT * x == BOT.
Proof.
  apply not_conv_eq_bot.
  apply not_conv_heads_bot.
  heads.
Qed.
Hint Rewrite code_eq_ap_bot : code_simpl.


Section Omega.
  Context {Var : Set}.
  Let x := make_var Var 0.
  Definition Omega := Eval compute in close_var ((\x, x * x) * (\x, x * x)).
  Goal Omega = S * I * I * (S * I * I).
  Proof.
    reflexivity.
  Qed.
End Omega.

Lemma code_le_omega_bot (Var : Set) : (@Omega Var) [= BOT.
Proof.
  unfold Omega, code_le; intros Var' c f Ha.
  induction Ha.
  simpl in H.
  (* TODO enumerate pi-reachable terms, then show TOP is not reachable *)
Admitted.

Lemma code_eq_omega_bot (Var : Set) : (@Omega Var) == BOT.
Proof.
  split ; (apply code_le_omega_bot || auto).
Qed.
