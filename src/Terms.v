(** * Lambda calculus with parametric de Bruijn terms *)

(**
  We use the parametric de Bruijn convention of
  https://coq.inria.fr/cocorico/UntypedLambdaTerms
  and earlier Bird and Patterson \cite{bird1999bruijn}.
  See also Capretta and Felty \cite{capretta2007combining}.
*)

Definition Succ := S%nat.  (* an alias for later *)

Require Export Notations.

(** ** Terms *)

Inductive Term {Var : Set} : Set :=
  | TOP : Term
  | BOT : Term
  | JOIN : Term -> Term -> Term
  | RAND : Term -> Term -> Term
  | APP : Term -> Term -> Term
  | VAR : Var -> Term
  | LAMBDA : @Term (option Var) -> Term
.
Arguments Term : default implicits.
Hint Constructors Term.
Definition Closed := Term Empty_set.

Notation "x * y" := (APP x y) : term_scope.
Open Scope term_scope.
Delimit Scope term_scope with term.
Bind Scope term_scope with Term.

Notation "x * y" := (APP x y) : term_scope.
Notation "x || y" := (JOIN x y) : term_scope.
Notation "x (+) y" := (RAND x y) : term_scope.

(** ** Lambda notation *)

Fixpoint iter {a : Type} (z : a) (s : a -> a) (n : nat) {struct n} :=
  match n with
  | 0 => z
  | Succ n' => s (iter z s n')
  end.

Fixpoint iter_dep
  {tz : Set} {ts : Set -> Set}
  (x : tz) (f : forall t : Set, t -> ts t) (n : nat) {struct n} :=
  match n return iter tz ts n with
  | 0 => x
  | Succ n' => f _ (iter_dep x f n')
  end.

Fixpoint iter_depT
  {tz : Type} {ts : Type -> Type}
  (x : tz) (f : forall t : Type, t -> ts t) (n : nat) {struct n} :=
  match n return iter tz ts n with
  | 0 => x
  | Succ n' => f _ (iter_depT x f n')
  end.

(* restrict [option] to [Set] level *)
Definition option' (a : Set) : Set := option a.
Definition Some' (a : Set) (x : a) : option' a := Some x.
Definition None' {a : Set} : option' a := None.

Definition option_ (n : nat) (v : Set) := iter v option' n.
Definition Some_ (n : nat) (v : Set) := iter_depT v Some n.
Definition lam_ {Var : Set} (n : nat) (x : Term (option_ n Var)) :=
  iter_dep x (@VAR) n.
(*
Definition var_ {Var : Set} (n : nat) : Term (option_ n Var) :=
  @VAR (option_ n Var) (iter_dep (@None' Var) Some' n).
*)

Section I.
  Definition v0 {Var : Set} : Term (option_ 1 Var) := VAR None.
  Definition v1 {Var : Set} : Term (option_ 2 Var) := VAR (Some None).
  Definition v2 {Var : Set} : Term (option_ 3 Var) := VAR (Some (Some None)).
  Context {Var : Set}.

  Definition I : Term Var := Eval compute in
    LAMBDA v0.
  Definition K : Term Var := Eval compute in
    LAMBDA (LAMBDA (VAR (Some None))).
  Definition B : Term Var := Eval compute in
    LAMBDA (LAMBDA (LAMBDA (v2 * (v1 * v0)))).
  Definition C : Term Var := Eval compute in
    LAMBDA (LAMBDA (LAMBDA (v2 * v0 * v1))).
  Definition S : Term Var := Eval compute in
    LAMBDA (LAMBDA (LAMBDA (v2 * v0 * (v1 * v0)))).
End I.
Print S.  (* Ugly! *)

Notation "x 'o' y" := (B * x * y) : term_scope.

Definition term_join {Var : Set} x y : Term Var := x || y.

(* TODO figure out how to use lambda notation
Notation "\ x , y" := (LAMBDA) : code_scope.
*)
