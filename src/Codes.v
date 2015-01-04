
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
  | beta_refl x : beta x x
  | beta_trans x y z : beta x y -> beta y z -> beta x z
  | beta_sym x y : beta x y -> beta y x
  | beta_ap_left x x' y : beta x x' -> beta (x * y) (x' * y)
  | beta_ap_right x y y' : beta y y' -> beta (x * y) (x * y')
  | beta_div_in x : beta (code_div * x) (code_div * (x * code_top))
  | beta_div_out : beta (code_div * code_top) code_top
  | beta_j x y z : beta ((x || y) * z) (x * z || y * z)
  | beta_j_left x : beta (code_top || x) code_top
  | beta_j_right x : beta (x || code_top) code_top
  | beta_i x : beta (code_i * x) x
  | beta_k x y : beta (code_k * x * y) x
  | beta_b x y z : beta (code_b * x * y * z) (x * (y * z))
  | beta_c x y z : beta (code_c * x * y * z) (x * z * y)
  | beta_s x y z : beta (code_s * x * y * z) (x * z * (y * z)).
Hint Constructors beta.

Definition conv x := beta (code_div * x) code_top.

Lemma conv_beta : forall x y, beta x y -> conv x -> conv y.
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
  | beta_ap_left x x' y : beta x x' -> beta (x * y) (x' * y)
  | beta_ap_right x y y' : beta y y' -> beta (x * y) (x * y')
  | beta_j x y z : beta ((x || y) * z) (x * z || y * z)
  | beta_j_left x : beta (code_top || x) code_top
  | beta_j_right x : beta (x || code_top) code_top
  | beta_i x : beta (code_i * x) x
  | beta_k x y : beta (code_k * x * y) x
  | beta_b x y z : beta (code_b * x * y * z) (x * (y * z))
  | beta_c x y z : beta (code_c * x * y * z) (x * z * y)
  | beta_s x y z : beta (code_s * x * y * z) (x * z * (y * z)).
Hint Constructors beta.

Inductive beta' : code -> code -> Prop :=
  | beta_step x y : beta x y -> beta' x y
  | beta_refl x : beta' x x
  | beta_trans x y z : beta' x y -> beta' y z -> beta' x z.

Inductive conv : code -> Prop :=
  | conv_top : conv code_top
  | conv_ap x : conv (x * code_top) -> conv x
  | conv_beta x y : beta x y -> conv y -> conv x.
Hint Constructors conv.

Definition code_le (x y : code) := forall c, conv (c * x) -> conv (c * y).
Definition code_eq (x y : code) : Prop := code_le x y /\ code_le y x.

Notation "x [= y" := (code_le x y) : code_scope.
Notation "x [=] y" := (code_eq x y) : code_scope.

Fixpoint code_apply (args : list code) (head : code) : code :=
  match args with
  | nil => head
  | cons arg args' => code_apply args' (head * arg)
  end.

Fixpoint code_apply' (args : list code) : code :=
  match args with
  | nil => code_i
  | cons arg args' => code_apply' args' o (code_c * code_i * arg)
  end.

Lemma code_apply_apply' :
  forall a x, beta' (code_apply' a * x) (code_apply a x).
Proof.
  intros a; induction a; compute.
    intro x; apply beta_step; apply beta_i.
  intro x; compute; fold code_apply; fold code_apply'.
  apply beta_trans with (code_apply' a0 * (code_c * code_i * a * x)).
  apply beta_step; auto.
  apply beta_trans with (code_apply' a0 * (code_i * x * a)).
  apply beta_step; auto.
  apply beta_trans with (code_apply' a0 * (x * a)).
  apply beta_step; auto.
  apply IHa.
Qed.

Theorem code_le_apply :
  forall x y, x [= y <->
  (forall a, conv (code_apply a x) -> conv (code_apply a y)).
Proof.
  intros x y; split.
    intros Hl a Hc.
Admitted.

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

Lemma less_refl : forall x, x [= x.
Proof.
  unfold code_le; intros x f; auto.
Qed.
Lemma less_trans : forall x y z, x [= y -> y [= z -> x [= z.
Proof.
  unfold code_le; intros x y z f g; auto.
Qed.
Lemma less_ap_left : forall x x' y, x [= x' -> x * y [= x' * y.
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
Lemma less_ap_right : forall x y y', y [= y' -> x * y [= x * y'.
Proof.
  unfold code_le; intros x y y' Hless c Hconv.
  apply conv_beta' with (code_b * c * x * y'); auto.
  apply Hless.
  apply conv_beta with (c * (x * y)); auto.
Qed.
Lemma less_ap : forall x x' y y', x [= x' -> y [= y' -> x * y [= x' * y'.
Proof.
  intros x x' y y' Hx Hy.
  apply less_trans with (x * y').
  apply less_ap_right; assumption.
  apply less_ap_left; assumption.
Qed.

Fixpoint probe (n : nat) (x : code) : code :=
  match n with
  | 0%nat => x
  | (S n')%nat => (probe n' x) * code_top
  end.

Lemma probe_bot_top : forall n, probe n code_bot <> code_top.
Proof.
  intros n; induction n; compute; fold probe; discriminate.
Qed.

Lemma beta_probe_bot : forall n x, ~ beta (probe n code_bot) x.
Proof.
  intros n x H; induction n.
    compute in H; inversion H.
  compute in H; fold probe in H.
  (* TODO *)
Admitted.

Lemma div_probe_bot : forall n : nat, ~ conv (probe n code_bot).
Proof.
  intros n H; inversion H.
      symmetry in H1; eapply probe_bot_top; apply H1.
Admitted.

(*  TODO

    This is very difficult to prove given the definitions of
    [code], [beta], and [conv].

    See sandbox/hoas.v which adds substitution and
    attempts to strengthen [conv] to get induction to work.
*)

Lemma less_bot_x : forall x, code_bot [= x.
Proof.
  unfold code_le.
  intros c H.
  inversion H.
  (* TODO *)
Admitted.

Lemma less_k_j : code_k [= code_j.
Proof.
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

Lemma less_join : forall x y z, x || y [= z <-> x [= z /\ y [= z.
Proof.
  intros x y z; split.
    intros Hxy; split.
    unfold code_le; intros c Hconv.
  (* TODO *)
Admitted.

Lemma join_idem : forall x, x || x [=] x.
Admitted.
Lemma join_assoc : forall x y z, x || (y || z) [=] (x || y) || z.
Admitted.
Lemma less_antisym : forall x y, (x [= y /\ y [= x) <-> x = y.
Admitted.

(** ** Indexed codes *)

(** Dependently typed indexed codes require up-front work in
    certifying an enumeration.
    We can make code construction easier by omitting this certificate,
    at the expense of more complicated uses of codes in
    [codes_ap] and [codes_le].
    *)

Definition precodes := {index : Type & index -> code}.

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

Definition predirect (x : precodes) : precodes :=
  let (index, enum) := x in
  let index' := tree index in
  let enum' := tree_reduce code_bot enum code_join in
  existT _ index' enum'.

Definition precodes_ap (s1 s2 : precodes) : precodes :=
  let (index1, enum1) := s1 in
  let (index2, enum2) := predirect s2 in
  let index12 := (index1 * index2)%type in
  let enum12 (i : index12) :=
    let (i1, i2) := i in (enum1 i1) * (enum2 i2)
  in
  existT _ index12 enum12.

(** patently Pi02 *)
Definition precodes_le (s1 s2 : precodes) : Prop :=
  let (index1, enum1) := predirect s1 in
  let (index2, enum2) := predirect s2 in
  forall c : code,
  forall i1 : index1, conv (c * (enum1 i1)) ->
  exists i2 : index2, conv (c * (enum2 i2)).

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

(** Now we demonstrate the power of indexing over directed sets.
    The simple implicit definition of [A_implicit] is not directed. *)

Definition direct (p : precodes) : codes.
  destruct p as [index enum].
  refine (codes_intro (tree index) (tree_reduce code_bot enum code_join) _ _).
    intros i j.
    exists (tree_pair _ i j).
    apply less_antisym.
    compute; auto.
  apply tree_none.
Defined.

Definition codes_sup {index : Type} (enum : index -> code) : codes :=
  direct (existT _ index enum).

Section direct_example.
  Open Scope code_scope.
  Let I := code_i.
  Variable pair : code -> code ->code.
  Notation "<< x , y >>" := (pair x y).
  Let A_implicit :=
    codes_sup (<<s, r>> for s : code for r : code if r o s [= I).
End direct_example.
