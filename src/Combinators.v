(** * Combinatory algebra with parametric variables *)

Definition Succ := S%nat.  (* an alias for later *)

Require Import Coq.Program.Basics.
Require Import Coq.Setoids.Setoid.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Arith.EqNat.
Require Export InformationOrdering.

(** ** Abstraction *)

(** Simple I,K,S-abstraction *)

Fixpoint code_abs0 {Var Var' : Set} (b : Var -> option Var') (x : Code Var) :
  Code Var' :=
  match x with
  | code_var v =>
      match b v with
      | None => I
      | Some v' => K * (code_var v')
      end
  | l * r => S * code_abs0 b l * code_abs0 b r
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

(** Efficient I,K,B,C,S,eta-abstraction *)

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
      | K * l', I => l'
      | K * l', K * r' => K * (l' * r')
      | K * l', r' => B * l' * r'
      | l', K * r' => C * l' * r'
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

Section code_eq_abs_sub.
  Variable Var Var' : Set.
  Variable b : Var -> option Var'.
  Variable x : Code Var.
  Variable y : Code Var'.
  Let f v := match b v with None => y | Some v' => code_var v' end.

  Lemma code_eq_abs0_sub : code_abs0 b x * y == code_sub f x.
  Proof.
    induction x; try (unfold f; simpl; auto; fail).
      unfold f; simpl; destruct (b v); beta_simpl; auto.
    rewrite code_sub_ap.
    unfold code_abs0; fold (@code_abs0 Var).
    rewrite beta_s; auto.
  Qed.

  Lemma code_eq_abs_abs0 : code_abs b x * y == code_abs0 b x * y.
  Proof.
    induction x; unfold f; simpl; auto.
    rewrite beta_s.
    rewrite <- IHc1; clear IHc1.
    rewrite <- IHc2; clear IHc2.
    destruct (code_abs b c1);
    destruct (code_abs b c2);
    try rewrite beta_s; auto;
    reflexivity || (
        destruct c3; try rewrite beta_s; beta_simpl; auto; reflexivity || (
            destruct c5; try rewrite beta_s; beta_simpl; auto
    )).
  Qed.

  Lemma code_eq_abs_sub : code_abs b x * y == code_sub f x.
  Proof.
    transitivity (code_abs0 b x * y);
    [apply code_eq_abs_abs0 | apply code_eq_abs0_sub].
  Qed.
End code_eq_abs_sub.
Hint Resolve code_eq_abs_sub.

(** ** Informal lambda notation *)

Definition make_var (Var : Set) (n : nat) : Code (nat + Var) :=
  code_var (@inl nat Var n).

Definition open {Var : Set} (x : Code Var) : Code (nat + Var) :=
  code_sub (fun v => code_var (inr v)) x.

Definition close {Var : Set} (x : Code (nat + Var)) : Code Var :=
  code_sub (fun v => match v with inr v' => code_var v' | _ => code_top end) x.

Lemma close_open (Var : Set) (x : Code Var) : close (open x) = x.
Proof.
  unfold close, open.
  induction x; simpl; auto.
  rewrite IHx1; rewrite IHx2; auto.
Qed.

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
    (\f, (\x, f * (x * x)) * (\x, f * (x * x))).
    (* ((\x, \f, f * (x * x * f)) * (\x, \f, f * (x * x * f))). *)
End Y.

Lemma code_eq_y (Var : Set) (f : Code Var) : Y * f == f * (Y * f).
Proof.
  unfold Y.
  rewrite beta_s at 1.
  rewrite beta_c at 1.
  rewrite beta_b at 1.
  rewrite beta_s at 1.
  rewrite beta_i.
  rewrite <- beta_s at 1.
  reflexivity.
Qed.

Section V.
  Context {Var : Set}.
  Let a := make_var Var 0.
  Let x := make_var Var 1.
  Definition V := Eval compute in close (\a, Y * \x, I || a o x).
End V.

Lemma code_eq_v (Var : Set) (a : Code Var) : V * a == I || a o (V * a).
Proof.
  unfold V at 1; fold (@Y Var).
  rewrite beta_b at 1.
  rewrite code_eq_y.
  rewrite <- (beta_right beta_b) at 1.
  unfold Y; fold (@V Var).
  beta_simpl; reflexivity.
Qed.

Lemma code_eq_v' (Var : Set) (a : Code Var) : V * a == I || (V * a) o a.
Proof.
Admitted.

(* The [div] combinator is useful in convergence testing *)

Definition div {Var : Set} : Code Var := Eval compute in V * (C * I * TOP).

Lemma code_eq_div (Var : Set) (x : Code Var) : div * x == x || div * x * TOP.
Proof.
  unfold div; fold (@V Var).
  rewrite code_eq_v at 1; beta_simpl; auto.
Qed.

Lemma code_eq_div' (Var : Set) (x : Code Var) :
  div * x == x || div * (x * TOP).
Proof.
  unfold div; fold (@V Var).
  rewrite code_eq_v' at 1; beta_simpl; auto.
Qed.

Lemma conv_div (Var : Set) (x : Code Var) : conv x <-> conv (div * x).
Proof.
  split; intro Hc.
    rewrite code_eq_div.
    rewrite test_j_left.
    auto.
  admit.
Qed.

Lemma conv_div_top (Var : Set) (x : Code Var) :
  conv x <-> div * x == TOP.
Proof.
  split.
    (* OLD
    intro H; induction H; split; auto; intros Var' c f Hc.
      rewrite H; rewrite code_eq_div; rewrite pi_j_left; auto.
    rewrite code_eq_div'; rewrite pi_j_right; rewrite IHconv; auto.
    *)
    admit.
  intros [H' H]; clear H'; unfold code_le in H.
  (* rewrite <- var_monad_unit_right; rewrite <- beta_i. *)
  assert (conv (I * (TOP @ code_var) : Code Var)) as Ht; code_simpl; auto.
  set (Hd := H Var I code_var Ht).
  code_simpl in Hd.
  apply conv_div; auto.
Qed.
