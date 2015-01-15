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
  | step_beta f x: step (APP (ABS (f Var)) x) (Subs f x)
  | step_app_1 f f' x: step f f' -> step (APP f x) (APP f' x)
  | step_app_2 f x x': step x x' -> step (APP f x) (APP f x')
  | step_abs f f' :
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

(** * Combinators *)

Inductive code :=
  | TOP : code
  | S : code
  | K : code
  | AP : code -> code -> code.

Notation "x ** y" := (AP x y) (at level 20, left associativity).

Fixpoint decode {Var : Set} (e : code) : Var -> Term Var :=
  fun top =>
  match e with
  | TOP => VAR top
  | S => [x] [y] [z] VAR x * VAR z * (VAR y * VAR z)
  | K => [x] [y] VAR x
  | AP e0 e1 => APP (decode e0 top) (decode e1 top)
  end.

(* FIXME
Fixpoint encode (e : forall Var, Term Var) : code :=
  match e bool with
  | VAR_ e0 => TOP   (* can this ever happen? *)
  | APP_ e0 e1 => AP (encode e0) (encode e1)
  | ABS_ e0 =>
    match e0 true with
    | VAR_ true => S ** K ** K
    | APP_ e1 e2 => S ** (encode ([x] e1 (VAR x))) ** (encode ([x] e2 (VAR x)))
    | ABS_ e1 => TOP
    end
  end.
*)
