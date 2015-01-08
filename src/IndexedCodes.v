
Require Import Setoid.
Require Export Codes.

(** ** Indexed codes *)

(** Now that we have defined finite codes,
    we would next like to define limits of finite codes,
    exactly mirroring the completion of the rationals as the reals.
    We will define limits as equivalence classes of finite codes
    indexed over directed sets,
    which are indexed sets together with a directedness certificate.
    We begin with codes indexed by undirected sets,
    i.e. sets without proof certificates of directedness. *)

Definition precodes (Var : Set) := {index : Type & index -> Code Var}.

Inductive tree (a : Type) : Type :=
  | tree_none : tree a
  | tree_leaf (x : a) : tree a
  | tree_pair (l r : tree a) : tree a.

Fixpoint tree_reduce {a b : Type}
  (f0 : b) (f1 : a -> b) (f2 : b -> b -> b) (t :tree a) : b :=
  match t with
  | tree_none => f0
  | tree_leaf x => f1 x
  | tree_pair l r => f2 (tree_reduce f0 f1 f2 l) (tree_reduce f0 f1 f2 r)
  end.

Definition predirect {Var : Set} (x : precodes Var) : precodes Var :=
  let (index, enum) := x in
  let index' := tree index in
  let enum' := tree_reduce code_bot enum code_join in
  existT _ index' enum'.

Definition precodes_ap {Var : Set} (s1 s2 : precodes Var) : precodes Var :=
  let (index1, enum1) := s1 in
  let (index2, enum2) := predirect s2 in
  let index12 := (index1 * index2)%type in
  let enum12 (i : index12) :=
    let (i1, i2) := i in (enum1 i1) * (enum2 i2)
  in
  existT _ index12 enum12.

(** patently Pi02 *)
Definition precodes_le {Var : Set} (s1 s2 : precodes Var) : Prop :=
  let (index1, enum1) := predirect s1 in
  let (index2, enum2) := predirect s2 in
  forall c : code,
  forall i1 : index1, conv (c * (enum1 i1)) ->
  exists i2 : index2, conv (c * (enum2 i2)).

(** Indexed codes with directedness certificates *)

Record codes {Var : Set} := codes_intro {
  index : Type;
  enum : index -> Code Var;
  join i1 i2 : {i : index | (enum i1 || enum i2 [= enum i)%code};
  nonempty : index
}.

Definition Codes (Var : Set) := @codes Var.
(*
Definition codes {Var : Set} := Codes Var.
*)

Definition codes_code {Var : Set} (x : Code Var) : Codes Var.
  refine (codes_intro Var unit (fun _  => x) (fun _ _ => _) tt).
  exists tt; auto.
Defined.

Section Codes_ap.
  Variable Var : Set.
  Variable s1 s2 : Codes Var.

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

  Definition Codes_ap : Codes Var.
    refine (codes_intro _ index12 enum12 _ nonempty12).
    intros i j.
    destruct i as [i1 i2].
    destruct j as [j1 j2].
    assert (kp1 := join1 i1 j1); destruct kp1 as [k1 p1].
    assert (kp2 := join2 i2 j2); destruct kp2 as [k2 p2].
    exists (k1, k2).
    unfold enum12.
    apply code_le_join in p1.
    apply code_le_join in p2.
    apply code_le_join; split; apply code_le_ap; apply p1 || apply p2.
  Defined.
End Codes_ap.

Definition codes_ap {Var : Set} := Codes_ap Var.

Notation "x * y" := (codes_ap x y) : codes_scope.

Open Scope codes_scope.
Delimit Scope codes_scope with codes.
Bind Scope codes_scope with codes.

(* does this require extensionality?
Lemma codess_ap_comm :
  forall x y, codess_ap (codess_codes x) (codess_codes y) = codess_codes (x * y).
Proof.
  intros x y.
  compute; auto.
*)

(** patently Pi02 *)
Definition codes_le {Var : Set} (s1 s2 : Codes Var) : Prop :=
  let (index1, enum1, _, _) := s1 in
  let (index2, enum2, _, _) := s2 in
  forall c : code,
  forall i1 : index1, conv (c * (enum1 i1))%code ->
  exists i2 : index2, conv (c * (enum2 i2))%code.

Definition codes_eq {Var : Set} (s s' : Codes Var) : Prop :=
  (codes_le s s' * codes_le s' s)%type.

Notation "x [= y" := (codes_le x y)%codes : codes_scope.
Notation "x [=] y" := (codes_eq x y)%codes : codes_scope.

(** Now we demonstrate the power of indexing over directed sets.
    The simple implicit definition of [A_implicit] is not directed. *)

Definition direct {Var : Set} (p : precodes Var) : Codes Var.
  destruct p as [index enum].
  refine (codes_intro _ (tree index) (tree_reduce BOT enum code_join) _ _).
    intros i j.
    exists (tree_pair _ i j).
    compute; auto.
  apply tree_none.
Defined.

Definition codes_sup {Var : Set} {index : Type} (enum : index -> Code Var) :
  Codes Var :=
  direct (existT _ index enum).

Section direct_example.
  Variable Var : Set.
  Open Scope code_scope.
  Notation "<< x , y >>" := (code_tuple (x::y::nil)%list).
  Let A_implicit : Codes Var :=
    codes_sup (<<s, r>> for s : code for r : code if r o s [= I).
End direct_example.
