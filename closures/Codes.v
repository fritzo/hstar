
Require Import Setoid.

(** * Extensional Combinatory Algebra

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

Lemma join_idem: forall x, x || x = x.
Admitted.
Lemma join_assoc: forall x y z, x || (y || z) = (x || y) || z.
Admitted.
Lemma less_antisym: forall x y, (x [= y /\ y [= x) <-> x = y.
Admitted.
Lemma less_refl: forall x, x [= x.
Admitted.
Lemma less_trans: forall x y z, x [= y -> y [= z -> x [= z.
Admitted.
Lemma less_ap: forall x x' y y', x [= x' -> y [= y' -> x * y [= x' * y'.
Admitted.
Lemma less_join: forall x y z, x || y [= z <-> x [= z /\ y [= z.
Admitted.

(** ** Indexed codes *)

(** We introduce directed sets of codes *)

Record codes := codes_intro {
  index : Type;
  enum : index -> code;
  join i1 i2 : {i : index | (enum i1 || enum i2 [= enum i)%code};
  nonempty : index
}.

Definition codes_code (x : code) : codes.
  refine (codes_intro unit (fun _ => x) (fun _ _ => _) tt).
  exists tt.
  rewrite join_idem.
  apply less_refl.
Defined.

Section codes_ap.
  Variable s1 s2 : codes.

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

  Definition codes_ap : codes.
    refine (codes_intro index12 enum12 _ nonempty12).
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
  Defined.
End codes_ap.

(** patently Pi02 *)
Definition codes_le (s1 s2 : codes) : Prop :=
  let (index1, enum1, _, _) := s1 in
  let (index2, enum2, _, _) := s2 in
  forall c : code,
  forall i1 : index1, conv (c * (enum1 i1)) ->
  exists i2 : index2, conv (c * (enum2 i2)).

Definition codes_eq (s s' : codes) : Prop :=
  (codes_le s s' * codes_le s' s)%type.

Notation "x [= y" := (codes_le x y)
  (at level 60, no associativity) : codes_scope.
Notation "x [=] y" := (codes_eq x y)
  (at level 60, no associativity) : codes_scope.

Open Scope codes_scope.
Delimit Scope codes_scope with codes.
Bind Scope codes_scope with codes.

(** Now we demonstrate the power of indexing over directed sets. *)

Section pre_codes.
  Open Scope code.
  Definition pre_codes := {index : Type & index -> code}.

  Fixpoint list_join {t : Type} (e : t -> code) (l : list t) : code :=
    match l with
    | nil => code_bot
    | (i :: l')%list => e i || list_join e l'
    end.

  Lemma list_join_assoc:
    forall (t : Type) (e : t -> code) (l l' : list t),
      list_join e l || list_join e l' = list_join e (l ++ l').
    intros t e.
    induction l.
    induction l'.
  Admitted.

  Definition make_codes (p : pre_codes) : codes.
    destruct p as [index enum].
    apply codes_intro with (index := list index) (enum := list_join enum).
      intros i j.
      exists (i ++ j)%list.
      apply less_antisym.
      symmetry.
      apply list_join_assoc.
    apply nil.
  Defined.
End pre_codes.

(*  The simple implicit definition of A_implicit is not directed.
    One solution is to define arbitrary sets of codes,
    and then their directed closure. *)

Section A_implicit.
  Definition BOT' : code.
  Admitted.
  Definition I : code.
  Admitted.
  Definition compose : code -> code -> code.
  Admitted.
  Definition pair : code -> code ->code.
  Admitted.

  Let code2 := (code * code)%type.
  Let index := {sr : code2 & let (s,r) := sr in (compose r s [= I)%code}.
  Let enum (sr : index) : code := match sr with existT (s, r) _ => pair s r end.
  Definition A_implicit' : codes.
    apply make_codes; unfold pre_codes.
    exists index; apply enum.
  Defined.
  Print A_implicit'.
  Definition A_implicit : codes := make_codes (existT _ index enum).
End A_implicit.

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

