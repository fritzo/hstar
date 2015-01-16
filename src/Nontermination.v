(** * Proofs of divergence / nontermination *)

Require Export InformationOrdering.
Open Scope code_scope.

Lemma beta_self_div (Var : Set) (x : Code Var) :
  (forall ys z, beta (x ** ys) z -> x ** ys = z) -> ~ conv x.
Proof.
Admitted.

Lemma beta_self_div' (Var : Set) (x : Code Var) :
  conv x -> exists ys z, beta (x ** ys) z /\ x ** ys <> z.
Proof.
Admitted.

Fixpoint probe {Var : Set} (n : nat) (x : Code Var) : Code Var :=
  match n with
  | 0%nat => x
  | (Succ n')%nat => (probe n' x) * code_top
  end.

Lemma probe_bot_top (Var : Set) : forall n, probe n (@code_bot Var) <> TOP.
Proof.
  intros n; induction n; compute; fold (@probe Var); discriminate.
Qed.

Lemma approx_probe_bot_top (Var : Set) :
  forall n, ~ approx (probe n (@code_bot Var)) TOP.
Proof.
  intros n H; induction n; auto.
Admitted.

Lemma div_probe_bot (Var : Set) :
  forall n : nat, ~ conv (probe n (@code_bot Var)).
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
  unfold Omega, code_le, conv; intros Var' c f Ha.
  induction Ha.
  (* TODO this could be proved from an asymmetric definition of beta *)
Admitted.

Lemma code_eq_omega_bot (Var : Set) : (@Omega Var) == BOT.
Proof.
  split ; (apply code_le_omega_bot || auto).
Qed.
