(** * Static analysis of inadvertently typed terms. *)

Require Import Coq.Setoids.Setoid.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Terms.
Require Import BohmTrees.

Definition V {Var : Set} : Term Var. Admitted.
Definition P {Var : Set} : Term Var. Admitted.
Definition div {Var : Set} : Term Var. Admitted.
Definition semi {Var : Set} : Term Var. Admitted.
(*
Definition bool {Var : Set} : Term Var. Admitted.
Definition prod {Var : Set} : Term Var. Admitted.
Definition sum {Var : Set} : Term Var. Admitted.
Definition exp {Var : Set} : Term Var. Admitted.
*)


(* Generically:
Module dependent.
  Record TypeTable := {
    TypeId : Set;
    get_type (Var : Set) :
      TypeId -> {t : Term Var | t :: V};
    get_id {Var : Set} (t : Term Var) :
      {i | proj1_sig (get_type Var i) = t} +
      {forall i, ~ proj1_sig (get_type Var i) = t};
    is_inhabitant {Var : Set} (x : Term Var) (i : TypeId) :
      let t := proj1_sig (get_type Var i) in
      {x :: t} + {~ x :: t} + {~ normal x};
    is_subtype {Var : Set} (i i' : TypeId) :
      let t := proj1_sig (get_type Var i) in
      let t' := proj1_sig (get_type Var i') in
      {t :: P * t'} + {~t :: P * t'}
  }.
End dependent.

Module factored.
  Record TypeTable := {
    TypeId : Set;
    get_type (Var : Set) : TypeId -> Term Var;
    get_id {Var : Set} : Term Var -> option TypeId;
    is_inhabitant {Var : Set} : Term Var -> TypeId -> option bool;
    is_subtype : TypeId -> TypeId -> bool;

    get_type_correct (Var : Set) (i : TypeId) : get_type Var i :: V;
    get_id_correct (Var : Set) (t : Term Var) :
      match get_id t with
      | Some i => get_type Var i = t
      | None => forall i, ~ get_type Var i = t
      end;
    is_inhabitant_correct (Var : Set) (x : Term Var) (i : TypeId) :
      let t := get_type Var i in
      if is_inhabitant x i
      then x :: t
      else normal x -> ~ x :: t;
    is_subtype_correct (Var : Set) (i i' : TypeId) :
      let t := get_type Var i in
      let t' := get_type Var i' in
      if is_subtype i i'
      then t :: P * t'
      else ~t :: P * t'
  }.
End factored.
*)

Inductive type : Set :=
  | type_any : type
  | type_nil : type
  | type_type : type
  | type_div : type
  | type_semi : type
  | type_bool : type
  | type_prod : type
  | type_sum : type
  (* Can these be eliminated?
  | type_sub : type -> type
  | type_both : type -> type -> type
  *)
  | type_exp : type -> type -> type.

Definition type_to_term (Var : Set) : type -> Term Var. Admitted.
Definition term_to_type {Var : Set} : Term Var -> option type. Admitted.
Definition is_inhabitant {Var : Set} : Term Var -> type -> option bool.
Admitted.
Definition is_subtype : type -> type -> bool. Admitted.
Definition unify_types : type -> type -> type. Admitted.

Lemma type_to_term_correct (Var : Set) (i : type) : type_to_term Var i :: V.
Admitted.

Lemma term_to_type_correct (Var : Set) (t : Term Var) :
  match term_to_type t with
  | Some i => type_to_term Var i = t
  | None => forall i, ~ type_to_term Var i = t
  end.
Admitted.

Lemma is_inhabitant_correct (Var : Set) (x : Term Var) (i : type) :
  let t := type_to_term Var i in
  if is_inhabitant x i
  then x :: t
  else normal x -> ~ x :: t.
Admitted.

Lemma is_subtype_correct (Var : Set) (i i' : type) :
  let t := type_to_term Var i in
  let t' := type_to_term Var i' in
  if is_subtype i i'
  then t :: P * t'
  else ~t :: P * t'.
Admitted.

Lemma unify_types_correct (Var : Set) (t t' : type) :
  let tt' := unify_types t t' in
  let a := type_to_term Var t in
  let a' := type_to_term Var t' in
  let aa' := type_to_term Var tt' in
  aa' == P * a * a'.
Admitted.

(* How to add types this? *)
Inductive tnormal {Var : Set} : Term Var -> Set :=
  | tnormal_top : tnormal TOP
  | tnormal_bot : tnormal BOT
  | tnormal_join x y : tnormal x -> tnormal y -> tnormal (x || y)
  | tnormal_rand x y : tnormal x -> tnormal y -> tnormal (x (+) y)
  | tnormal_app x y : tinert x -> tnormal y -> tnormal (x * y)
  | tnormal_lambda x : @tnormal (option Var) x -> tnormal (LAMBDA x)
  | tnormal_var v : tnormal (VAR v)
with tinert {Var : Set} : Term Var -> Set :=
  | tinert_var v : tinert (VAR v)
  | tinert_app x y : tinert x -> tnormal y -> tinert (x * y).
Hint Constructors tnormal tinert.

(* an example of how to use an induction principle *)

Theorem semi_ind (Var : Set) (p q : Term Var) :
  p * TOP [= q * TOP ->
  p * BOT [= q * BOT ->
  p * I [= q * I ->
  p o semi [= q o semi.
Admitted.

Definition try_decide_inhab_semi {Var : Set} (x : Term Var) :
  {x :: semi} + {~ x :: semi} + {~ normal x}.
Proof.
  set (is_normal_x := is_normal x).
  case_eq is_normal_x; intro Hn.
  - apply inleft.
    apply normal_is_normal in Hn.
    (* TODO apply semi_ind *)
    admit.
  - apply inright; intro Hn'.
    subst; apply normal_is_normal in Hn'; rewrite Hn' in Hn; inversion Hn.
Qed.
