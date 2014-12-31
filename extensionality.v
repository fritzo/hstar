
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

(** ** Arbitrary indexed codes *)

(*
Record codex := {
  index : Type;
  enum : index -> code;
  join : forall (p : index -> Type),
    {i : index & forall i', p i' -> (enum i' [= enum i)%code}
}.
*)

(* We introduce directed sets of codes *)

Record codex := codex_intro {
  index : Type;
  enum : index -> code;
  join i1 i2 : {i : index | (enum i1 || enum i2 [= enum i)%code};
  nonempty : index
}.

Section less_lemmas.
  Open Scope code.
  Lemma join_idem: forall x, x || x = x.
  Admitted.
  Lemma less_refl: forall x, x [= x.
  Admitted.
  Lemma less_trans: forall x y z, x [= y -> y [= z -> x [= z.
  Admitted.
  Lemma less_ap: forall x x' y y', x [= x' -> y [= y' -> x * y [= x' * y'.
  Admitted.
  Lemma less_join: forall x y z, x || y [= z <-> x [= z /\ y [= z.
  Admitted.
End less_lemmas.

Definition codex_inject (x : code) : codex.
  eapply codex_intro with (index := unit) (enum := fun _ => x).
    intros i1 i2; elim i1; elim i2.
    exists tt.
    rewrite join_idem.
    apply less_refl.
  apply tt.
Defined.

Section codex_ap.
  Open Scope code.

  Parameter s1 : codex.
  Parameter s2 : codex.

  Let index1 := s1.(index).
  Let enum1 := s1.(enum).
  Let join1 := s1.(join).
  Let nonempty1 := s1.(nonempty).

  Let index2 := s2.(index).
  Let enum2 := s2.(enum).
  Let join2 := s2.(join).
  Let nonempty2 := s2.(nonempty).

  Let index12 := (index1 * index2)%type.

  Let enum12 (i : index12) : code :=
    let (i1, i2) := i in
    (enum1 i1) * (enum2 i2).

  Let nonempty12 := (nonempty1, nonempty2).

  Definition codex_ap : codex.
    apply codex_intro with (index := index12) (enum := enum12).
      intros i j.
      destruct i as [i1 i2].
      destruct j as [j1 j2].
      assert (kp1 := join1 i1 j1); destruct kp1 as [k1 p1].
      assert (kp2 := join2 i2 j2); destruct kp2 as [k2 p2].
      exists (k1, k2).
      unfold enum12.
      apply less_join in p1.
      apply less_join in p2.
      apply less_join; split; apply less_ap; apply p1 || apply p2.
    apply nonempty12.
  Defined.
End codex_ap.

(* patently Pi02 *)
Definition codex_le (s1 s2 : codex) : Prop :=
  let (index1, enum1, _, _) := s1 in
  let (index2, enum2, _, _) := s2 in
  forall c : code,
  forall i1 : index1, conv (c * (enum1 i1)) ->
  exists i2 : index2, conv (c * (enum2 i2)).

Definition codex_eq (s s' : codex) : Prop :=
  (codex_le s s' * codex_le s' s)%type.

Notation "x [= y" := (codex_le x y)
  (at level 60, no associativity) : codex_scope.
Notation "x [=] y" := (codex_eq x y)
  (at level 60, no associativity) : codex_scope.

Open Scope codex_scope.
Delimit Scope codex_scope with codex.
Bind Scope codex_scope with codex.

(* Now we demonstrate the power of indexing over directed sets. *)

Definition BOT' : code.
Admitted.
Definition I : code.
Admitted.
Definition compose : code -> code -> code.
Admitted.
Definition pair : code -> code ->code.
Admitted.

(*  The simple implicit definition of A_implicit is not directed.
    One solution is to define arbitrary sets of codes,
    and then their directed closure.

Definition A_implicit : codex := {|
  index := { sr : (code * code)%type
           | let (s,r) := sr in (compose r s [= I)%code};
  enum := fun i => match i with exist (s, r) _ => pair s r end;
  join := (* FIXME this cannot be defined *);
  nonempty := (BOT', BOT')
|}.

*)
