
Require Import EqNat.

Reserved Notation "x * y" (at level 40, left associativity).
Reserved Notation "x 'o' y" (at level 30, right associativity).
Reserved Notation "x || y" (at level 50, left associativity).
Reserved Notation "x (+) y" (at level 45, no associativity).
Reserved Notation "x [= y" (at level 60, no associativity).
Reserved Notation "x [=] y" (at level 60, no associativity).
Reserved Notation "x [!= y" (at level 60, no associativity).
Reserved Notation "x ->> y" (at level 60, no associativity).
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
  | beta_refl x : beta x x
  | beta_trans x y z : beta x y -> beta y z -> beta x z
  | beta_ap_left x x' y : beta x x' -> beta (x * y) (x' * y)
  | beta_ap_right x y y' : beta y y' -> beta (x * y) (x * y')
  | beta_top x : beta code_top x
  | beta_bot x : beta x code_bot
  | beta_j x y z : beta ((x || y) * z) (x * z || y * z)
(*
  | beta_j_left x : beta (code_top || x) code_top
  | beta_j_right x : beta (x || code_top) code_top
*)
  | beta_j_left x y : beta (x || y) x
  | beta_j_right x y : beta (x || y) y
  | beta_i x : beta (code_i * x) x
  | beta_k x y : beta (code_k * x * y) x
  | beta_b x y z : beta (code_b * x * y * z) (x * (y * z))
  | beta_c x y z : beta (code_c * x * y * z) (x * z * y)
  | beta_s x y z : beta (code_s * x * y * z) (x * z * (y * z)).
Hint Constructors beta.
(* Notation "x ->> y" := (beta x y) : code_scope. *)

Inductive conv {Var : Set} : Code Var -> Prop :=
  | conv_ap x : conv (x * code_top) -> conv x
  | conv_beta x : beta x code_top -> conv x.
Hint Constructors conv.

(** ** Substitution and abstraction *)

Fixpoint code_sub {Var Var' : Set}
  (f : Var -> Code Var') (x : Code Var) : Code Var' :=
  match x with
  | Code_var v => f v
  | Code_ap l r => (code_sub f l) * (code_sub f r)
  | Code_top => code_top
  | Code_bot => code_bot
  | Code_j => code_j
  | Code_i => code_i
  | Code_k => code_k
  | Code_b => code_b
  | Code_c => code_c
  | Code_s => code_s
  end.
Hint Resolve code_sub.

Lemma var_monad_unit (Var : Set) (x : Code Var) : code_sub code_var x = x.
Proof.
  induction x; auto.
  unfold code_sub; fold (@code_sub Var Var).
  rewrite IHx1; rewrite IHx2; auto.
Qed.

Lemma var_monad_unit_left (Var Var' : Set) (f : Var -> Code Var') x :
  code_sub f (code_var x) = f x.
Proof.
  compute; auto.
Qed.

Lemma var_monad_assoc
  (Var Var' Var'' : Set)
  (f : Var -> Code Var')
  (g : Var' -> Code Var'')
  (x : Code Var) :
  code_sub g (code_sub f x) = code_sub (fun v => code_sub g (f v)) x.
Proof.
  (* TODO *)
Admitted.

Fixpoint code_abs {Var Var' : Set} (b : Var -> option Var') (x : Code Var) :
  Code Var' :=
  match x with
  | Code_var v =>
      match b v with
      | None => code_i
      | Some v' => code_k * (code_var v')
      end
  | Code_ap l r => code_s * (code_abs b l) * (code_abs b r)
  | Code_top => code_k * code_top
  | Code_bot => code_k * code_bot
  | Code_j => code_k * code_j
  | Code_i => code_k * code_i
  | Code_k => code_k * code_k
  | Code_b => code_k * code_b
  | Code_c => code_k * code_c
  | Code_s => code_k * code_s
  end.

Lemma abs_sub_beta {Var Var' : Set}
  (b : Var -> option Var') (x : Code Var) (y : Code Var') :
  beta (code_abs b x * y)
       (code_sub (fun v => match b v with None => y
                                        | Some v' => code_var v' end) x).
Proof.
  induction x; simpl; auto.
    case (b v); [intro v'; auto | auto].
  apply beta_trans with (code_abs b x1 * y * (code_abs b x2 * y)); auto.
  apply beta_trans with
    (code_abs b x1 * y
    * (code_sub (fun v => match b v with None => y
                                       | Some v' => code_var v' end) x2)); auto.
Qed.

(*
Definition beta_sub :
  forall {Var Var' : Set} (f : Var -> Code Var') {u v : Code Var},
  beta u v -> beta (code_sub f u) (code_sub f v)
.
  intros Var Var' f u v beta.
  induction beta; auto.
*)

Fixpoint beta_sub {Var Var' : Set}
  (f : Var -> Code Var') {u v : Code Var} (b : beta u v) :
  beta (code_sub f u) (code_sub f v)
.
Admitted.
(* FIXME Coq is having trouble typing this
  :=
  let s := code_sub f in
  let f1 c x := c (s x) in
  let f2 c x y := c (s x) (s y) in
  let f3 c x y z := c (s x) (s y) (s z) in
  let s' := beta_sub f in
  match b, (s u, s v) return beta (s u) (s v) with
  | beta_refl x, _ => f1 beta_refl x
  | beta_trans x y z b1 b2, t =>
      f3 beta_trans x y z (beta_sub f b1) (beta_sub f b2)
  | beta_ap_left x x' y b1, t => f3 beta_ap_left x x' y (s' b1)
  | beta_ap_right x y y' b1, t => f3 beta_ap_right x y y' (s' b1)
  | beta_top x, t => f1 beta_top x
  | beta_bot x, t => f1 beta_bot x
  | beta_j x y z, t => f3 beta_j x y z
  | beta_j_left x y, t => f2 beta_j_left x y
  | beta_j_right x y, t => f2 beta_j_right x y
  | beta_i x, t => f1 beta_i x
  | beta_k x y, t => f2 beta_k x y
  | beta_b x y z, t => f3 beta_b x y z
  | beta_c x y z, t => f3 beta_c x y z
  | beta_s x y z, t => f3 beta_s x y z
  end.
*)

(** Sloppy lambda notation specialized to [Code nat] *)

Definition nat_match (m n : nat) : option nat :=
  if beq_nat m n then None else Some m.

Definition code_lambda (v : Code nat) (x : Code nat) : Code nat :=
  match v with
  | Code_var n => code_abs (nat_match n) x
  | _ => code_top (* TODO implement pattern matching here*)
  end.

Notation "\ x , y" := (code_lambda x y)%code : code_scope.

(** Contexts, convergence, and information ordering *)

Inductive context (Var Var' : Set) : Set :=
  context_intro : (Var -> Code Var') -> Code (option Var') -> context Var Var'.

Fixpoint context_sub {Var Var' : Set}
  (c : context Var Var') (x : Code Var) : Code Var' :=
  let (c1, c2) := c in
  let x' := code_sub c1 x in
  let f v := match v with None => x' | Some v' => code_var v' end in
  code_sub f c2.

Definition conv_in {Var Var' : Set}
  (c : context Var Var') (x : Code Var) : Prop :=
  conv (context_sub c x).

Definition code_le {Var : Set} (x y : Code Var) : Prop :=
  forall (Var' : Set) (c : context Var Var'), conv_in c x -> conv_in c y.

(*  TODO

    Strengthen the definitions of [beta] [conv] and [code_le]
    so that the following lemmas follow by induction.
*)

Lemma code_le_x_top {Var : Set} (x : Code Var) : code_le x code_top.
Proof.
  unfold code_le; unfold conv_in; intros Var' c Hconv.
  elim Hconv; simpl; auto.
  intros x' Hbeta.
  induction Hbeta; auto.
Admitted.

Lemma code_le_bot_x {Var : Set} (x : Code Var) : code_le code_bot x.
Proof.
  unfold code_le; intros Var' c Hconv.
  induction c; simpl; auto.
  induction Hconv.
Admitted.

Lemma code_le_k_j {Var : Set} : @code_le Var code_k code_j.
Proof.
  unfold code_le; intros Var' c Hconv.
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
