(** * Some standard combinators *)

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

Section code_eq_abs0_sub.
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
End code_eq_abs0_sub.

Instance code_abs0_proper_le (Var Var' : Set) :
  Proper (eq ==> code_le ==> code_le) (@code_abs0 Var Var').
Proof.
  intros b b' bb' x x' xx'.
  code_le_weaken; intros ys f.
  induction ys.
  - assert (TOP @ f = TOP) as TOP_f; [simpl; auto|].
    simpl; rewrite <- bb'; intro Hc.
    rewrite ap_top_conv; rewrite ap_top_conv in Hc.
    rewrite <- TOP_f; rewrite <- TOP_f in Hc.
    rewrite <- code_sub_ap; rewrite <- code_sub_ap in Hc.
    rewrite code_eq_abs0_sub; rewrite code_eq_abs0_sub in Hc.
    rewrite xx' in Hc; assumption.
  - set (Ha := code_sub_inverse _ f a); destruct Ha as [a' aa'].
    simpl.
    repeat rewrite <- aa'.
    repeat rewrite <- code_sub_ap.
    repeat rewrite code_eq_abs0_sub.
    rewrite xx', bb'; firstorder.
Qed.

Instance code_abs0_proper_eq (Var Var' : Set) :
  Proper (eq ==> code_eq ==> code_eq) (@code_abs0 Var Var').
Proof.
  intros b b' bb' x x' [xx' x'x]; rewrite <- bb'.
  split; [rewrite xx' | rewrite x'x]; auto.
Qed.

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

  Lemma code_eq_abs_abs0_ext : code_abs b x * y == code_abs0 b x * y.
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
    [apply code_eq_abs_abs0_ext | apply code_eq_abs0_sub].
  Qed.
End code_eq_abs_sub.
Hint Resolve code_eq_abs_sub.

Lemma code_eq_abs_abs0
  (Var Var' : Set) (b : Var -> option Var') (x : Code Var) :
  code_abs b x == code_abs0 b x.
Proof.
  eta_expand as y; apply code_eq_abs_abs0_ext.
Qed.

Instance code_abs_proper_le (Var Var' : Set) :
  Proper (eq ==> code_le ==> code_le) (@code_abs Var Var').
Proof.
  intros b b' bb' x x' xx'.
  repeat rewrite code_eq_abs_abs0.
  rewrite bb', xx'; auto.
Qed.

Instance code_abs_proper_eq (Var Var' : Set) :
  Proper (eq ==> code_eq ==> code_eq) (@code_abs Var Var').
Proof.
  intros b b' bb' x x' xx'.
  repeat rewrite code_eq_abs_abs0.
  rewrite bb', xx'; auto.
Qed.

(** ** Informal lambda notation *)

Definition make_var (Var : Set) (n : nat) : Code (nat + Var) :=
  code_var (@inl nat Var n).

Definition open_var {Var : Set} (x : Code Var) : Code (nat + Var) :=
  code_sub (fun v => code_var (inr v)) x.

Definition close_var {Var : Set} (x : Code (nat + Var)) : Code Var :=
  code_sub (fun v => match v with inr v' => code_var v' | _ => code_top end) x.

Lemma close_open (Var : Set) (x : Code Var) : close_var (open_var x) = x.
Proof.
  unfold close_var, open_var.
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

Notation "\ x , y" := (code_lambda x y)%code : code_scope.

(** ** Standard combinators *)

Section Y.
  Context {Var : Set}.
  Let f := make_var Var 0.
  Let x := make_var Var 1.
  Definition Y := Eval compute in close_var
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
  Definition V := Eval compute in close_var (\a, Y * \x, I || a o x).
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

Lemma conv_div (Var : Set) (x : Code Var) : code_conv x <-> code_conv (div * x).
Proof.
  split; intro Hc.
    rewrite code_eq_div.
    rewrite pi_j_left.
    auto.
  admit. (* TODO use limit characterization of div and induction on probe *)
Qed.

Lemma conv_div_top (x : Code Empty_set) : code_conv x <-> div * x == TOP.
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
  assert (code_conv (I * (TOP @ code_var) : Code Empty_set)) as Ht; code_simpl; auto.
  set (Hd := H Empty_set I code_var Ht).
  code_simpl in Hd.
  apply conv_div; auto.
Qed.
