(** * Combinatory algebra with parametric variables *)

Definition Succ := S%nat.  (* an alias for later *)

Require Import Coq.Program.Basics.
Require Import Coq.Setoids.Setoid.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Arith.EqNat.
Require Export InformationOrdering.

(** ** Abstraction *)

Fixpoint code_abs {Var Var' : Set} (b : Var -> option Var') (x : Code Var) :
  Code Var' :=
  match x with
  | code_var v =>
      match b v with
      | None => I
      | Some v' => K * (code_var v')
      end
  | l * r =>
      match code_abs b l, code_abs b r with
      (* TODO switch to more efficient lambda abstraction once proof passes
      *)
      | K * l', I => l'
      | K * l', K * r' => K * (l' * r')
      | K * l', r' => B * l' * r'
      | l', K * r' => C * l' * r'
      (*
      *)
      | l', r' => S * l' * r'
      end
  | TOP => K * TOP
  | BOT => K * BOT
  | J => K * J
  | R => K * R
  | I => K * I
  | K => K * K
  | B => K * B
  | C => K * C
  | S => K * S
  end.

Section beta_abs_sub.
  Variable Var Var' : Set.
  Variable b : Var -> option Var'.
  Variable x : Code Var.
  Variable y : Code Var'.
  Let f v := match b v with None => y | Some v' => code_var v' end.

  Lemma beta_abs_sub : beta (code_abs b x * y) (code_sub f x).
  Proof.
    induction x; try (unfold f; simpl; auto; fail).
      compute; case (b v); auto.
    (* TODO this only works for simple I,K,S-abstraction.
    compute; rewrite beta_s.
    transitivity (code_abs b c1 * y * (code_sub f c2)); auto.
    *)
  Admitted.
End beta_abs_sub.
Hint Resolve beta_abs_sub.

(** ** Informal lambda notation *)

Definition make_var (Var : Set) (n : nat) : Code (nat + Var) :=
  code_var (@inl nat Var n).

Definition close {Var : Set} (x : Code (nat + Var)) : Code Var :=
  code_sub (fun v => match v with inr v' => code_var v' | _ => code_top end) x.

Definition code_lambda {Var : Set} (x y : Code (nat + Var)) :
  Code (nat + Var) :=
  let beq_var (v1 v2 : nat + Var) : bool :=
    match v1, v2 with
    | inl n1, inl n2 => beq_nat n1 n2
    | _, _ => false
    end
  in
  match x with
  | code_var v => code_abs (fun v' => if beq_var v v' then None else Some v') y
  | _ => BOT  (* TODO implement pattern matching here *)
  end.

Notation "\ x , y" := (code_lambda x y) : code_scope.

(** ** Standard combinators *)

Section Y.
  Context {Var : Set}.
  Let f := make_var Var 0.
  Let x := make_var Var 1.
  Definition Y := Eval compute in close
    ((\f, \x, f * (x * x * f)) * (\f, \x, f * (x * x * f))).
    (* (\f, (\x, f * (x * x)) * (\x, f * (x * x))).  *)
End Y.

Lemma beta_y (Var : Set) (f : Code Var) : beta (Y * f) (f * (Y * f)).
Proof.
  unfold Y.
Admitted.
Hint Rewrite beta_y : beta_unsafe.

Section V.
  Context {Var : Set}.
  Let a := make_var Var 0.
  Let x := make_var Var 1.
  Definition V := Eval compute in close (\a, Y * \x, I || a o x).
End V.

(* FIXME this is only true up to undirected [beta_eta] *)
Lemma beta_v (Var : Set) (a : Code Var) : beta (V * a) (I || a o (V * a)).
Proof.
  unfold V; fold (@Y Var).
Admitted.
Hint Rewrite beta_v : beta_unsafe.

(* The [div] combinator is useful in convergence testing *)

Definition div {Var : Set} : Code Var := Eval compute in V * (C * I * TOP).

Lemma beta_div (Var : Set) (x : Code Var) :
  beta (div * x) (x || div * x * TOP).
Proof.
  unfold div; fold (@V Var).
  rewrite beta_v at 1; beta_simpl; auto.
Qed.
Hint Rewrite beta_div : beta_unsafe.

Lemma conv_div (Var : Set) (x : Code Var) :
  conv x <-> div * x == TOP.
Proof.
  split.
  intro H; induction H.
      admit.
    admit.
  intros [H' H]; clear H'.
  unfold code_le in H.
Admitted.
