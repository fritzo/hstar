(** * Reasoning about nontermination *)

Require Export Combinators.
Open Scope code_scope.

Definition sub_top {Var : Set} (Var' : Set) (x : Var) : Code Var' := TOP.

Lemma conv_sub_top (Var Var' : Set) (x : Code Var) (f : Var -> Code Var') :
  conv (x @ f) -> conv (x @ sub_top Var').
Proof.
  induction x; simpl; intros; auto.
Admitted.

Lemma not_conv_eq_bot (Var : Set) (x : Code Var) :
  ~ conv (x @ sub_top Var) -> x == BOT.
Proof.
  intro Hd; split; auto.
  apply code_le_apply_equiv; unfold code_le_apply.
  unfold code_le; intros Var' c f Hc.
  (* TODO
  apply conv_sub_top in Hc.
  *)
Admitted.

Lemma beta_self_div (Var : Set) (x : Code Var) :
  (forall ys z, beta (x ** ys) z -> x ** ys = z) -> ~ conv x.
Proof.
Admitted.

Lemma beta_self_div' (Var : Set) (x : Code Var) :
  conv x -> exists ys z, beta (x ** ys) z /\ x ** ys <> z.
Proof.
Admitted.

Fixpoint probed {Var : Set} (n : nat) (x : Code Var) : Code Var :=
  match n with
  | 0%nat => x
  | (Succ n')%nat => (probed n' x) * code_top
  end.

Lemma probe_bot_top (Var : Set) : forall n, probed n (@code_bot Var) <> TOP.
Proof.
  intros n; induction n; compute; fold (@probed Var); discriminate.
Qed.

(* OLD
Lemma approx_probe_bot_top (Var : Set) :
  forall n, ~ approx (probed n (@code_bot Var)) TOP.
Proof.
  intros n H; induction n; auto.
Admitted.
*)

Lemma ap_top_div (Var : Set) (x : Code Var) : div * (x * TOP) == div * x.
Proof.
Admitted.

Lemma div_ap_top (Var : Set) (x : Code Var) : div * x * TOP == div * x.
Proof.
  (* OLD
  split.
    rewrite beta_div at 2; rewrite pi_j_right; auto.
  unfold code_le, conv; intros Var' c f H.
  simpl in *; auto.
  *)
Admitted.

Lemma div_repeat_top (Var : Set) (x : Code Var) (n : nat) :
  (div * x) ** TOP ^^ n == div * x.
Proof.
  induction n; simpl; auto.
Admitted.

Lemma repeat_top_div (Var : Set) (x : Code Var) (n : nat) :
  div * (x ** TOP ^^ n) == div * x.
Proof.
  induction n; simpl; auto.
Admitted.

Lemma div_probe_bot (Var : Set) :
  forall n : nat, ~ conv (probed n (@code_bot Var)).
Proof.
  intros n H; inversion H.
Admitted.

Lemma div_bot (Var : Set) : div * BOT == (BOT : Code Var).
Proof.
  unfold div.
  (* TODO this could be proved from an asymmetric definition of beta *)
Admitted.
Hint Rewrite div_bot : code_simpl.

Section Omega.
  Context {Var : Set}.
  Let x := make_var Var 0.
  Definition Omega := Eval compute in close ((\x, x * x) * (\x, x * x)).
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
