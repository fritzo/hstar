
Require Import Setoid.
Require Export FunctionalExtensionality.

(** * Extensional combinatory algebra.

    This development implements a quotient construction
    using five retraction axioms. *)

(** ** Codes *)

Inductive code : Set :=
  | code_ap : code -> code -> code
  | code_top : code
  | code_bot : code
  | code_j : code
  | code_k : code
  | code_s : code.

Notation "x * y" := (code_ap x y)
  (at level 40, left associativity) : code_scope.

Open Scope code_scope.
Delimit Scope code_scope with code.
Bind Scope code_scope with code.

Notation "x || y" := (code_j * x * y)%code
  (at level 50, left associativity) : code_scope.

Inductive red : code -> code -> Prop :=
  | red_ap_left x x' y: red x x' -> red (x * y) (x' * y)
  | red_ap_right x y y': red y y' -> red (x * y) (x * y')
  | red_j x y z: red ((x || y) * z) (x * z || y * z)
  | red_j_left x: red (code_top || x) code_top
  | red_j_right x: red (x || code_top) code_top
  | red_k x y: red (code_k * x * y) x
  | red_s x y z: red (code_s * x * y * z) (x * z * (y * z)).

Inductive conv : code -> Prop :=
  | conv_top: conv code_top
  | conv_ap x: conv (x * code_top) -> conv x
  | conv_red x y: red x y -> conv x -> conv y.

Inductive code_le (x y : code) : Prop :=
  less_intro: (forall c, conv (c * x) -> conv (c * y)) -> code_le x y.

Notation "x [= y" := (code_le x y)
  (at level 60, no associativity) : code_scope.

(** ** Sequences of codes *)

CoInductive codes : Set := push: code -> codes -> codes.
CoFixpoint monotonize_ (bot : code) (s : codes) : codes :=
  let (x, s') := s in
  let x' := bot || x in
  push x' (monotonize_ x' s').
Definition monotonize := monotonize_ code_bot.

CoFixpoint monotone_codes_ap (s s' : codes) :=
  let (x, s) := s in
  let (x', s') := s' in
  push (code_ap x x') (monotone_codes_ap s s').
Definition codes_ap (s s' : codes) := monotone_codes_ap s (monotonize s').

CoFixpoint exactly (x : code) := push x (exactly x).

Fixpoint codes_at (s : codes) (n : nat) :=
  match n, s with
  | 0%nat, push x _ => x
  | (S n')%nat, push _ s' => codes_at s' n'
  end.

(* patently Pi02 *)
Definition codes_le (s s' : codes) : Prop :=
  let s := monotonize s in
  let s' := monotonize s' in
  forall c : code,
  forall n : nat,
  conv (c * (codes_at s n)) ->
  exists n' : nat,
  conv (c * (codes_at s n')).

Definition codes_eq (s s' : codes) : Prop :=
  (codes_le s s' * codes_le s' s)%type.

Notation "x [= y" := (codes_le x y)
  (at level 60, no associativity) : codes_scope.
Notation "x [=] y" := (codes_eq x y)
  (at level 60, no associativity) : codes_scope.

Open Scope codes_scope.
Delimit Scope codes_scope with codes.
Bind Scope codes_scope with codes.

(** ** Points *)

Axiom point : Set.
Axiom denote : codes -> point.
Axiom access : point -> codes.
Axiom denote_access : forall s, s = denote (access s).
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

Theorem consistency : ~ [exactly code_top] = [exactly code_bot].
Proof.
  (* TODO apply access_denote. *)
Admitted.

Definition definable (p : point) := {x : code & p = [exactly  x]}.

(** ** Standard combinators *)

Definition point_ap p p' := codes_ap (access p) (access p').

Notation "'TOP'" := ([exactly code_top]) : point_scope.
Notation "'BOT'" := ([exactly code_bot]) : point_scope.
Notation "'J'" := ([exactly code_j]) : point_scope.
Notation "'K'" := ([exactly code_k]) : point_scope.
Notation "'S'" := ([exactly code_s]) : point_scope.
Notation "p * p'" := (point_ap p p')%point : point_scope.
Notation "x || y" := (J * x * y)%point
  (at level 50, left associativity) : point_scope.

(*  FIXME is it safe to use arbitrary [Type]s instead of [nat]?
    It is very convenient to use arbitrarily indexed sets,
    especially when defining joins using comprehension and products. *)

(*
Definition code_set := {t : Type & t -> code}.
Definition directed (xs : code_set) :=
  let (t, e) := xs in
  forall (p : t -> Type),
  {i : t & forall ij : {i : t & p i}, let (i', j) := ij in e i' [= e i}.
Definition code_dset := {xs : code_set & directed xs}.

Definition exactly (x : code) : code_dset :=
  existT (existT unit (fun _ => p)) (fun (p : Type) (e : t -> p) =>.

Definition codes_le (xs xs' : code_dset) :=
  match xs with existT (existT t e) _ =>
    match xs' with existT (existT t' e') _ =>
      forall i : t, {i' : t' & code_le (e i) (e' i')}
    end
  end.
Definition codes_eq (xs xs' : code_dset) : Type :=
  (codes_le xs xs' * codes_le xs' xs)%type.
*)
