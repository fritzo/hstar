Inductive Term (Var : Type) : Type :=
  | VAR_ : Var -> Term Var
  | APP_ : Term Var -> Term Var -> Term Var
  | ABS_ : (Var -> Term Var) -> Term Var.

Definition term {Var : Type} := Term Var.
Definition VAR {Var : Type} := VAR_ Var.
Definition APP {Var : Type} := APP_ Var.
Definition ABS {Var : Type} := ABS_ Var.

Notation "x * y" := (APP x y) (at level 40, left associativity).
Notation "[ x ] y" := (ABS_ _ (fun x => y)) (at level 50).

Definition I {Var : Type} : Term Var := [x] VAR x.
Hint Unfold I.

Fixpoint squash {Var : Type} (e : Term (Term Var)) : Term Var :=
  match e with
  | VAR_ e => e
  | APP_ e0 e1 => APP (squash e0) (squash e1)
  | ABS_ f => ABS_ _ (fun x => squash (f (VAR x)))
  end.

Eval compute in (fun y => squash ([x] VAR x * VAR y)).

Definition Term1 := forall Var, Var -> Term Var.

Definition Subs {Var : Type} (f : forall Var, Var -> Term Var) (x : Term Var) :=
  squash (f (Term Var) x).

Eval compute in Subs (fun _ x => APP (VAR x) (VAR x)) I.

Inductive step {Var : Type} : Term Var -> Term Var -> Prop :=
  | step_beta: forall f x, step (APP (ABS (f Var)) x) (Subs f x)
  | step_app_1: forall f f' x, step f f' -> step (APP f x) (APP f' x)
  | step_app_2: forall f x x', step x x' -> step (APP f x) (APP f x')
  | step_abs: forall f f' : Term1,
      (forall v x, step (Var := v) (f v x) (f' v x)) ->
      step (ABS (f Var)) (ABS (f' Var))
.
Hint Constructors step.

Lemma step_identity: forall v (x : Term v), step (I * x) x.
Proof.
  intros.
  unfold I.
  apply step_beta.
Qed.

Definition Omega {Var : Type} : Term Var := APP ([x] VAR x * VAR x) ([x] VAR x * VAR x).
Lemma step_omega: forall v, step (Var := v) Omega Omega.
Proof.
  intros.
  unfold Omega.
  (* TODO
  apply step_beta.
  *)
Admitted.
