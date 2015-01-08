
Require Export IndexedCodes.

(** * Points as quotients of indexed codes.

    This development implements a quotient construction
    using five retraction axioms.
*)

Axiom Point : Set -> Set.
Axiom denote : forall {Var : Set}, Codes Var -> Point Var.
Axiom access : forall {Var : Set}, Point Var -> Codes Var.
Axiom denote_access : forall (Var : Set) (p : Point Var), p = denote (access p).
Axiom denote_respect :
  forall (Var : Set) (s s' : Codes Var), codes_eq s s' -> denote s = denote s'.

Lemma denote_respect' (Var : Set) (p p' : Point Var) :
    codes_eq (access p) (access p') -> p = p'.
Proof.
  intro H.
  rewrite denote_access.
  rewrite denote_access at 1.
  apply denote_respect.
  auto.
Qed.

Notation "[ x ]" := (denote (codes_code x)) : point_scope.

Definition point_le {Var : Set} (p p' : Point Var) :=
  codes_le (access p) (access p').
Definition point_eq {Var : Set} (p p' : Point Var) :=
  codes_eq (access p) (access p').

Notation "x [= y" := (point_le x y) : point_scope.
Notation "x [=] y" := (point_eq x y) : point_scope.

Open Scope point_scope.
Delimit Scope point_scope with point.
Bind Scope point_scope with Point.

Definition point_ap {Var : Set} (p p' : Point Var) :=
  denote (codes_ap (access p) (access p')).
Infix "*" := point_ap : point_scope.

Notation "'TOP'" := [code_top] : point_scope.
Notation "'BOT'" := [code_bot] : point_scope.
Notation "'J'" := [code_j] : point_scope.
Notation "'I'" := [code_i] : point_scope.
Notation "'K'" := [code_k] : point_scope.
Notation "'B'" := [code_b] : point_scope.
Notation "'C'" := [code_c] : point_scope.
Notation "'S'" := [code_s] : point_scope.
Notation "p * p'" := (point_ap p p')%point : point_scope.
Notation "x || y" := (J * x * y)%point : point_scope.

Definition sup {Var : Set} {i : Type} (e : i -> Code Var) : Point Var :=
  denote (codes_sup e).

Lemma point_ap_respect (Var : Set) (x y : Code Var) : [x] * [y] = [x * y]%code.
Proof.
  unfold point_ap; unfold codes_ap.
  (* TODO *)
Admitted.

Theorem consistency (Var : Set) : [@code_top Var] <> [@code_bot Var].
Proof.
  (* TODO apply access_denote. *)
Admitted.

Definition definable {Var : Set} (p : Point Var) := {x : code & p = [x]}.
