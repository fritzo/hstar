
Require Import EqNat.

Reserved Notation "x * y" (at level 40, left associativity).
Reserved Notation "x 'o' y" (at level 30, right associativity).
Reserved Notation "x || y" (at level 50, left associativity).
Reserved Notation "x (+) y" (at level 45, no associativity).
Reserved Notation "x [= y" (at level 60, no associativity).
Reserved Notation "x [=] y" (at level 60, no associativity).
Reserved Notation "x [!= y" (at level 60, no associativity).
Reserved Notation "\ x , y" (at level 0, right associativity).

Section Code.
  Variable Var : Set.
  Inductive Code : Set :=
    | Code_var : Var -> Code
    | Code_ap : Code -> Code -> Code
    | Code_top : Code
    | Code_bot : Code
    | Code_j : Code
    | Code_i : Code
    | Code_k : Code
    | Code_b : Code
    | Code_c : Code
    | Code_s : Code.
End Code.
Hint Constructors Code.

Definition code_var {Var : Set} := Code_var Var.
Definition code_ap {Var : Set} := Code_ap Var.
Definition code_top {Var : Set} := Code_top Var.
Definition code_bot {Var : Set} := Code_bot Var.
Definition code_j {Var : Set} := Code_j Var.
Definition code_i {Var : Set} := Code_i Var.
Definition code_k {Var : Set} := Code_k Var.
Definition code_b {Var : Set} := Code_b Var.
Definition code_c {Var : Set} := Code_c Var.
Definition code_s {Var : Set} := Code_s Var.

Notation "x * y" := (code_ap x y) : code_scope.

Open Scope code_scope.
Delimit Scope code_scope with code.
Bind Scope code_scope with Code.

Notation "x 'o' y" := (code_b * x * y)%code : code_scope.
Notation "x || y" := (code_j * x * y)%code : code_scope.

Inductive beta {Var : Set} : Code Var -> Code Var -> Prop :=
(*
  | beta_refl x : beta x x
  | beta_sym x y : beta x y -> beta y x
*)
  | beta_trans x y z : beta x y -> beta y z -> beta x z
  | beta_ap_left x x' y : beta x x' -> beta (x * y) (x' * y)
  | beta_ap_right x y y' : beta y y' -> beta (x * y) (x * y')
  | beta_top x : beta (code_top * x) code_top
  | beta_j x y z : beta ((x || y) * z) (x * z || y * z)
  | beta_j_left x : beta (code_top || x) code_top
  | beta_j_right x : beta (x || code_top) code_top
  | beta_i x : beta (code_i * x) x
  | beta_k x y : beta (code_k * x * y) x
  | beta_b x y z : beta (code_b * x * y * z) (x * (y * z))
  | beta_c x y z : beta (code_c * x * y * z) (x * z * y)
  | beta_s x y z : beta (code_s * x * y * z) (x * z * (y * z)).
Hint Constructors beta.

Inductive conv {Var : Set} : Code Var -> Prop :=
  | conv_ap x : conv (x * code_top) -> conv x
  | conv_beta x : beta x code_top -> conv x.
Hint Constructors conv.

Fixpoint code_sub {Var Var' : Set}
  (e : Var -> Code Var') (x : Code Var) : Code Var' :=
  match x with
  | Code_var v => e v
  | Code_ap l r => (code_sub e l) * (code_sub e r)
  | Code_top => code_top
  | Code_bot => code_bot
  | Code_j => code_j
  | Code_i => code_i
  | Code_k => code_k
  | Code_b => code_b
  | Code_c => code_c
  | Code_s => code_s
  end.

(* this version is a little sloppy *)
Fixpoint code_abs {Var : Set} (d : Var -> bool) (x : Code Var) : Code Var :=
  match x with
  | Code_var v => if d v then code_i else code_k * x
  | Code_ap l r => code_s * (code_abs d l) * (code_abs d r)
  | _ => code_k * x
  end.

(* this version is linear in [Var] *)
Fixpoint code_abs' {Var Var' : Set} (d : Var -> option Var') (x : Code Var) :
  Code Var' :=
  match x with
  | Code_var v =>
      match d v with
      | None => code_i
      | Some v' => code_k * (code_var v')
      end
  | Code_ap l r => code_s * (code_abs' d l) * (code_abs' d r)
  | Code_top => code_k * code_top
  | Code_bot => code_k * code_bot
  | Code_j => code_k * code_j
  | Code_i => code_k * code_i
  | Code_k => code_k * code_k
  | Code_b => code_k * code_b
  | Code_c => code_k * code_c
  | Code_s => code_k * code_s
  end.

Definition code_lambda (v : Code nat) (x : Code nat) : Code nat :=
  match v with
  | Code_var n => code_abs (beq_nat n) x
  | _ => code_top (* TODO implement pattern matching here*)
  end.

Notation "\ x , y" := (code_lambda x y)%code : code_scope.

Lemma abs_sub_beta {Var : Set} (d : Var -> bool) (x y : Code Var) :
  beta (code_abs d x * y)
       (code_sub (fun v => if d v then y else code_var v) x).
Proof.
  induction x; simpl; auto.
    case (d v); [auto | apply beta_k].
  apply beta_trans with (code_abs d x1 * y * (code_abs d x2 * y)); auto.
  apply beta_trans with
    (code_abs d x1 * y
    * (code_sub (fun v : Var => if d v then y else code_var v) x2)); auto.
Qed.

Definition conv_in {Var Var': Set}
  (e : Var -> Code Var') (c : Code (option Var')) (x : Code Var) : Prop :=
  let x' := code_sub e x in
  let e' v := match v with None => x' | Some v' => code_var v' end in
  let c' := code_sub e' c in
  conv c'.

Definition code_le {Var : Set} (x y : Code Var) : Prop :=
  forall {Var' : Set} (e : Var -> Code Var') (c : Code (option Var')),
    conv_in e c x -> conv_in e c y.

(*  TODO

    Strengthen the definitions of [beta] [conv] and [code_le]
    so that the following lemmas follow by induction.
*)

Lemma code_le_x_top {Var : Set} {x : Code Var} : code_le code_bot x.
Proof.
  unfold code_le; intros Var' e c Hconv.
  induction c; simpl; auto.
  induction Hconv.
Admitted.

Lemma code_le_bot_x {Var : Set} {x : Code Var} : code_le code_bot x.
Proof.
  unfold code_le; intros Var' e c Hconv.
  induction c; simpl; auto.
  induction Hconv.
Admitted.

Lemma code_le_k_j {Var : Set} : @code_le Var code_k code_j.
Proof.
  unfold code_le; intros Var' e c Hconv.
  induction c; simpl; auto.
  induction Hconv.
Admitted.

Lemma code_le_ap_left {Var : Set} {x x' y : Code Var} :
  code_le x x' -> code_le (x * y) (x' * y).
Admitted.

Lemma code_le_ap_right {Var : Set} {x y y': Code Var} :
  code_le y y' -> code_le (x * y) (x * y').
Admitted.

Lemma code_le_ap {Var : Set} {x x' y y': Code Var} :
  code_le x x' -> code_le y y' -> code_le (x * y) (x' * y').
Admitted.

Lemma code_le_subs {Var : Set} (d : Var -> bool) (x y y' : Code Var) :
  code_le y y' -> 
  code_le (code_sub (fun v => if d v then y else code_var v) x)
          (code_sub (fun v => if d v then y' else code_var v) x).
Admitted.

