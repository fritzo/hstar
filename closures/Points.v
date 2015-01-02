
Require Import Codes.

(** ** Points as quotients of indexed codes *)

Axiom point : Set.
Axiom denote : codes -> point.
Axiom access : point -> codes.
Axiom denote_access : forall p, p = denote (access p).
Axiom denote_respect : forall s s', codes_eq s s' -> denote s = denote s'.

Lemma denote_respect':
  forall p p' : point, codes_eq (access p) (access p') -> p = p'.
Proof.
  intros p p' H.
  rewrite denote_access.
  rewrite denote_access at 1.
  apply denote_respect.
  auto.
Qed.

Notation "[ e ]" := (denote e) : point_scope.

Definition point_le p p' := codes_le (access p) (access p').
Definition point_eq p p' := codes_eq (access p) (access p').

Notation "x [= y" := (point_le x y)
  (at level 60, no associativity) : point_scope.
Notation "x [=] y" := (point_eq x y)
  (at level 60, no associativity) : point_scope.

Open Scope point_scope.
Delimit Scope point_scope with point.
Bind Scope point_scope with point.

Theorem consistency : ~ [codes_code code_top] = [codes_code code_bot].
Proof.
  (* TODO apply access_denote. *)
Admitted.

Definition definable (p : point) := {x : code & p = [codes_code  x]}.

(** ** Standard combinators *)

Definition point_ap p p' := codes_ap (access p) (access p').

Notation "'TOP'" := ([codes_code code_top]) : point_scope.
Notation "'BOT'" := ([codes_code code_bot]) : point_scope.
Notation "'J'" := ([codes_code code_j]) : point_scope.
Notation "'K'" := ([codes_code code_k]) : point_scope.
Notation "'S'" := ([codes_code code_s]) : point_scope.
Notation "p * p'" := (point_ap p p')%point : point_scope.
Notation "x || y" := (J * x * y)%point
  (at level 50, left associativity) : point_scope.
