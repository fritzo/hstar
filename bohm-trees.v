Inductive Combinator : Set :=
  | BOT : Combinator
  | TOP : Combinator
  | K : Combinator
  | S : Combinator
  (*
  | ROT : nat -> Combinator
  *)
  | AP : Combinator -> Combinator -> Combinator.

Notation "x * y" := (AP x y) (at level 40, left associativity).

(*
Inductive LambdaTerm : Set :=
  | BOT : LambdaTerm
  | TOP : LambdaTerm
  | AP : LambdaTerm -> LambdaTerm -> LambdaTerm
  | VAR : nat -> LambdaTerm
  | ABS : nat -> LambdaTerm -> LambdaTerm.

Fixpoint abstract (n : nat) (x : LambdaTerm) :=
  match x with
  | AP u v => S * (abstract n u) (abstract n v)
  end.

Fixpoint compile (u : LambdaTerm) : Combinator
  match u with
  | BOT => BOT
  | AP v w => AP (compile v) (compile w)
  | ABS n v => abstract n v
  end.
*)

Inductive reduces : Combinator -> Combinator -> Prop :=
  | red_refl : forall x, reduces x x
  | red_trans : forall x y z, reduces x y -> reduces y z -> reduces x z
  | red_ap_1 : forall x x0 y, reduces x x0 -> reduces (x*y) (x0*y)
  | red_ap_2 : forall x y y0, reduces y y0 -> reduces (x*y) (x*y0)
  | red_top : forall x, reduces TOP x
  | red_bot : forall x, reduces x BOT
  | red_k : forall x y, reduces (K*x*y) x
.

Inductive solvable : Combinator -> Prop :=
  | conv_red : forall x, reduces x TOP -> solvable x
  | conv_ap : forall x, solvable (AP x TOP) -> solvable x
.

Definition less (x : Combinator) (y : Combinator) : Prop :=
  forall f, solvable (f * x) -> solvable (f * y).
Definition equiv (x : Combinator) (y : Combinator) : Prop :=
  forall f, solvable (f * x) <-> solvable (f * y).


Notation "x [= y" := (less x y) (at level 60).
Notation "x [=] y" := (equiv x y) (at level 60).

Lemma equiv_less: forall x y, equiv x y <-> less x y /\ less y x.
Proof.
  (* TODO *)
Admitted.

(** * Head normal form and %B\"ohm% trees *)

Inductive hnf0 : Combinator -> Prop :=
  | hnf0_k: hnf0 K
  | hnf0_s: hnf0 S
  | hnf0_s2: forall x y, hnf0 x -> hnf0 (S*x*y)
.

Inductive hnf : Combinator -> Prop :=
  | hnf_hnf0: forall x, hnf0 x -> hnf x
  | hnf_k: forall x, hnf0 x -> hnf (K*x)
  | hnf_s1: forall x, hnf x -> hnf (S*x)
  | hnf_s2: forall x y, hnf x -> hnf (S*x*y)
.

Theorem hnf_exists: forall x, solvable x -> exists y, reduces x y /\ hnf y.
Proof.
  (* TODO *)
Admitted.

(** * A definable tool for type checking *)

Definition div := V*(C*I*TOP).

Definition raise := K. (* \x,y. x *)
Definition lower := C*I*TOP. (* \x. x TOP *)
Definition pull := J*K*(K*div). (* \x,y. x | div y *)
Definition push := C*I*BOT. (* \x. x _ *)

Notation "< x , y >" := (B*(C*I*y)*(C*I*x)).

Definition A : Combinator := (
  Y\s. <I, I>
     | <raise, lower>
     | <pull, push>
     | (s\a,a'. s\b,b'. <a*b, b'*a'>)
     | (s\a,a'. s\b,b'. <(a'->b), (a->b')>)
).

Theorem A_soundness: A * CB [= I.
Proof.
  (* TODO *)
Admitted.

Theorem A_completeness: forall s r, (B*r*s) [= I -> <s,r> [= A.
Proof.
  (* TODO *)
Admitted.

(** * Inhabitants of polymorphic types *)

Theorem semi_inhab: forall x, semi*x [=] BOT \/ semi*x [=] I \/ semi*x [=] TOP.
Proof.
  (* TODO *)
Admitted.
