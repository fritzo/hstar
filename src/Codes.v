
Require Import Setoid.
Require Export Notations.

(** * Extensional Combinatory Algebra

    This development implements a quotient construction
    using five retraction axioms. *)

(** ** Codes *)

(* This version moves [conv] into [code] as [code_div].

Inductive code' : Set :=
  | code_ap : code -> code -> code
  | code_top : code
  | code_bot : code
  | code_div : code
  | code_j : code
  | code_i : code
  | code_k : code
  | code_b : code
  | code_c : code
  | code_s : code.

Notation "x * y" := (code_ap x y) : code_scope.
Open Scope code_scope.
Delimit Scope code_scope with code.
Bind Scope code_scope with code.
Notation "x 'o' y" := (code_b * x * y)%code : code_scope.
Notation "x || y" := (code_j * x * y)%code : code_scope.

Inductive beta : code -> code -> Prop :=
  | beta_refl x: beta x x
  | beta_trans x y z: beta x y -> beta y z -> beta x z
  | beta_sym x y: beta x y -> beta y x
  | beta_ap_left x x' y: beta x x' -> beta (x * y) (x' * y)
  | beta_ap_right x y y': beta y y' -> beta (x * y) (x * y')
  | beta_div_in x: beta (code_div * x) (code_div * (x * code_top))
  | beta_div_out: beta (code_div * code_top) code_top
  | beta_j x y z: beta ((x || y) * z) (x * z || y * z)
  | beta_j_left x: beta (code_top || x) code_top
  | beta_j_right x: beta (x || code_top) code_top
  | beta_i x: beta (code_i * x) x
  | beta_k x y: beta (code_k * x * y) x
  | beta_b x y z: beta (code_b * x * y * z) (x * (y * z))
  | beta_c x y z: beta (code_c * x * y * z) (x * z * y)
  | beta_s x y z: beta (code_s * x * y * z) (x * z * (y * z)).
Hint Constructors beta.

Definition conv x := beta (code_div * x) code_top.

Lemma conv_beta: forall x y, beta x y -> conv x -> conv y.
Proof.
  unfold conv; intros x y Hbeta Hx.
  apply beta_trans with (code_div * x).
    apply beta_ap_right;
    apply beta_sym;
    assumption.
  assumption.
Qed.

*)

Inductive code : Set :=
  | code_ap : code -> code -> code
  | code_top : code
  | code_bot : code
  | code_j : code
  | code_i : code
  | code_k : code
  | code_b : code
  | code_c : code
  | code_s : code.

Notation "x * y" := (code_ap x y) : code_scope.

Open Scope code_scope.
Delimit Scope code_scope with code.
Bind Scope code_scope with code.

Notation "x 'o' y" := (code_b * x * y)%code : code_scope.
Notation "x || y" := (code_j * x * y)%code : code_scope.

Definition code_join x y := x || y.

Inductive beta : code -> code -> Prop :=
  | beta_ap_left x x' y: beta x x' -> beta (x * y) (x' * y)
  | beta_ap_right x y y': beta y y' -> beta (x * y) (x * y')
  | beta_j x y z: beta ((x || y) * z) (x * z || y * z)
  | beta_j_left x: beta (code_top || x) code_top
  | beta_j_right x: beta (x || code_top) code_top
  | beta_i x: beta (code_i * x) x
  | beta_k x y: beta (code_k * x * y) x
  | beta_b x y z: beta (code_b * x * y * z) (x * (y * z))
  | beta_c x y z: beta (code_c * x * y * z) (x * z * y)
  | beta_s x y z: beta (code_s * x * y * z) (x * z * (y * z)).
Hint Constructors beta.

Inductive conv : code -> Prop :=
  | conv_top: conv code_top
  | conv_ap x: conv (x * code_top) -> conv x
  | conv_beta x y: beta x y -> conv y -> conv x.
Hint Constructors conv.

Definition code_le (x y : code) := forall c, conv (c * x) -> conv (c * y).
Definition code_eq (x y : code) : Prop := code_le x y /\ code_le y x.

Notation "x [= y" := (code_le x y) : code_scope.
Notation "x [=] y" := (code_eq x y) : code_scope.

(*
Ltac abstract M x :=
  match m with
  | x => code_ap code_i x
  | code_ap ?M1 ?M2 =>
    let code_ap N1 _ := abstract M1 x in
    let code_ap N2 _ := abstract M2 x in
    code_ap (code_ap (code_ap code_s N1) N2) x
  | _ => code_ap code_k x
  end.

Ltac beta_subs :=
  match goal with
  | beta x y
*)

Lemma conv_beta' : forall x y, beta x y -> conv x -> conv y.
Proof.
  intros x y Hbeta Hx.
  destruct Hx; inversion Hbeta.
  (* TODO *)
Admitted.

Lemma less_refl: forall x, x [= x.
Proof.
  unfold code_le; intros x f; auto.
Qed.
Lemma less_trans: forall x y z, x [= y -> y [= z -> x [= z.
Proof.
  unfold code_le; intros x y z f g; auto.
Qed.
Lemma less_ap_left: forall x x' y, x [= x' -> x * y [= x' * y.
Proof.
  unfold code_le; intros x x' y Hless c Hconv.
  apply conv_beta' with (c * (code_i * x' * y)); auto.
  apply conv_beta' with (c * (code_c * code_i * y * x')); auto.
  apply conv_beta' with (code_b * c * (code_c * code_i * y) * x'); auto.
  apply Hless.
  apply conv_beta with (c * (code_c * code_i * y * x)); auto.
  apply conv_beta with (c * (code_i * x * y)); auto.
  apply conv_beta with (c * (x * y)); auto.
Qed.
Lemma less_ap_right: forall x y y', y [= y' -> x * y [= x * y'.
Proof.
  unfold code_le; intros x y y' Hless c Hconv.
  apply conv_beta' with (code_b * c * x * y'); auto.
  apply Hless.
  apply conv_beta with (c * (x * y)); auto.
Qed.
Lemma less_ap: forall x x' y y', x [= x' -> y [= y' -> x * y [= x' * y'.
Proof.
  intros x x' y y' Hx Hy.
  apply less_trans with (x * y').
  apply less_ap_right; assumption.
  apply less_ap_left; assumption.
Qed.
Lemma less_k_j: code_k [= code_j.
Proof.
  unfold code_le.
  unfold code_le.
  intros c H.
  inversion H.
  (* TODO *)
Admitted.
Lemma less_join_left : forall x y, x [= x || y.
Proof.
  intros x y0; generalize y0 as y; clear y0.
  (* TODO *)
Admitted.
Lemma less_join: forall x y z, x || y [= z <-> x [= z /\ y [= z.
Proof.
  intros x y z; split.
    intros Hxy; split.
    unfold code_le; intros c Hconv.
  (* TODO *)
Admitted.
Lemma join_idem: forall x, x || x [=] x.
Admitted.
Lemma join_assoc: forall x y z, x || (y || z) [=] (x || y) || z.
Admitted.
Lemma less_antisym: forall x y, (x [= y /\ y [= x) <-> x = y.
Admitted.

(** ** Dependently typed indexed codes *)

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
  apply join_idem.
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

(* does this require extensionality?
Lemma codes_ap_comm :
  forall x y, codes_ap (codes_code x) (codes_code y) = codes_code (x * y).
Proof.
  intros x y.
  compute; auto.
*)

(** patently Pi02 *)
Definition codes_le (s1 s2 : codes) : Prop :=
  let (index1, enum1, _, _) := s1 in
  let (index2, enum2, _, _) := s2 in
  forall c : code,
  forall i1 : index1, conv (c * (enum1 i1)) ->
  exists i2 : index2, conv (c * (enum2 i2)).

Definition codes_eq (s s' : codes) : Prop :=
  (codes_le s s' * codes_le s' s)%type.

Notation "x [= y" := (codes_le x y) : codes_scope.
Notation "x [=] y" := (codes_eq x y) : codes_scope.

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
  Definition compose : code -> code -> code.
  Admitted.
  Definition pair : code -> code ->code.
  Admitted.

  Let code2 := (code * code)%type.
  Let index := {sr : code2 & let (s,r) := sr in (compose r s [= code_i)%code}.
  Let enum (sr : index) : code := match sr with existT (s, r) _ => pair s r end.
  Definition A_implicit' : codes.
    apply make_codes; unfold pre_codes.
    exists index; apply enum.
  Defined.
  Print A_implicit'.
  Definition A_implicit : codes := make_codes (existT _ index enum).
End A_implicit.

(** ** Indexed codes *)

(** Dependently typed indexed codes require up-front work in
    certifying an enumeration.
    We can make code construction easier by omitting this certificate,
    at the expense of more complicated uses of codes in
    [codes_ap] and [codes_le].
    *)

Definition codes' := {index : Type & index -> code}.

Inductive tree (a : Type) : Type :=
  | tree_leaf (x : a) : tree a
  | tree_pair (l r : tree a) : tree a.

Hint Constructors tree.

Fixpoint tree_reduce {a b : Type}
  (f1 : a -> b) (f2 : b -> b -> b) (t :tree a) : b :=
  match t with
  | tree_leaf x => f1 x
  | tree_pair l r => f2 (tree_reduce f1 f2 l) (tree_reduce f1 f2 r)
  end.

Definition finite_joins_of (x : codes') : codes' :=
  let (index, enum) := x in
  let index' := tree index in
  let enum' := tree_reduce enum code_join in
  existT _ index' enum'.

Definition codes_ap' (s1 s2 : codes') : codes' :=
  let (index1, enum1) := s1 in
  let (index2, enum2) := finite_joins_of s2 in
  let index12 := (index1 * index2)%type in
  let enum12 (i : index12) :=
    let (i1, i2) := i in (enum1 i1) * (enum2 i2)
  in
  existT _ index12 enum12.

(** patently Pi02 *)
Definition codes_le' (s1 s2 : codes') : Prop :=
  let (index1, enum1) := finite_joins_of s1 in
  let (index2, enum2) := finite_joins_of s2 in
  forall c : code,
  forall i1 : index1, conv (c * (enum1 i1)) ->
  exists i2 : index2, conv (c * (enum2 i2)).
