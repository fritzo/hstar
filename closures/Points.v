
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

Notation "[ x ]" := (denote (codes_code x)) : point_scope.

Definition point_le p p' := codes_le (access p) (access p').
Definition point_eq p p' := codes_eq (access p) (access p').

Notation "x [= y" := (point_le x y) : point_scope.
Notation "x [=] y" := (point_eq x y) : point_scope.

Open Scope point_scope.
Delimit Scope point_scope with point.
Bind Scope point_scope with point.

Definition point_ap p p' := denote (codes_ap (access p) (access p')).
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

Lemma point_ap_respect : forall x y, [x] * [y] = [x * y].
Proof.
  intros x y.
  unfold point_ap.
  unfold codes_ap.
  (* TODO *)
Admitted.

Theorem consistency : ~ [code_top] = [code_bot].
Proof.
  (* TODO apply access_denote. *)
Admitted.

Definition definable (p : point) := {x : code & p = [x]}.
