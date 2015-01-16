(** * Reasoning about least fixed points *)

Require Import Coq.Program.Basics.
Require Import Coq.Setoids.Setoid.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Export InformationOrdering.
Open Scope code_scope.

Lemma Y_lfp (Var : Set) (f b : Code Var) :
  (forall x, x [= b -> f * x [= b) -> Y * f [= b.
Proof.
Admitted.
