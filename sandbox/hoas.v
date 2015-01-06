
Require Import Setoid.
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

Inductive code {Var : Set} : Set :=
  | code_var : Var -> code
  | code_ap : code -> code -> code
  | code_top : code
  | code_bot : code
  | code_j : code
  | code_i : code
  | code_k : code
  | code_b : code
  | code_c : code
  | code_s : code
  | code_y : code
  | code_v : code.
Hint Constructors code.
Definition Code (Var : Set) := @code Var.

Notation "x * y" := (code_ap x y) : code_scope.
Notation "'TOP'" := code_top : code_scope.
Notation "'BOT'" := code_bot : code_scope.
Notation "'J'" := code_j : code_scope.
Notation "'I'" := code_i : code_scope.
Notation "'K'" := code_k : code_scope.
Notation "'B'" := code_b : code_scope.
Notation "'C'" := code_c : code_scope.
Notation "'S'" := code_s : code_scope.
Notation "'Y'" := code_y : code_scope.
Notation "'V'" := code_v : code_scope.

Open Scope code_scope.
Delimit Scope code_scope with code.
Bind Scope code_scope with code.

Notation "x 'o' y" := (code_b * x * y)%code : code_scope.
Notation "x || y" := (code_j * x * y)%code : code_scope.

Inductive beta {Var : Set} : Code Var -> Code Var -> Prop :=
  | beta_refl x : beta x x
  | beta_trans x y z : beta x y -> beta y z -> beta x z
  | beta_ap_left x x' y : beta x x' -> beta (x * y) (x' * y)
  | beta_ap_right x y y' : beta y y' -> beta (x * y) (x * y')
  | beta_top x : beta TOP x
  | beta_bot x : beta x BOT
  | beta_j x y z : beta ((x || y) * z) (x * z || y * z)
  | beta_j_left x y : beta (x || y) x
  | beta_j_right x y : beta (x || y) y
  | beta_i x : beta (I * x) x
  | beta_k x y : beta (K * x * y) x
  | beta_b x y z : beta (B * x * y * z) (x * (y * z))
  | beta_c x y z : beta (C * x * y * z) (x * z * y)
  | beta_s x y z : beta (S * x * y * z) (x * z * (y * z))
  | beta_y x : beta (Y * x) (x * (Y * x))
  | beta_v x : beta (V * x) (I || x o (V * x)).
Hint Constructors beta.

Fixpoint try_beta_step {Var : Set} (u : Code Var) : option (Code Var) :=
  match u with
  | I * x => Some x
  | K * x * y => Some x
  | J * x * y * z => Some (x * z || y * z)
  | B * x * y * z => Some (x * (y * z))
  | C * x * y * z => Some (x * z * y)
  | S * x * y * z => Some (x * z * (y * z))
  | Y * x => Some (x * (Y * x))
  | V * x => Some (I || x o (V * x))
  | x * y =>
      match try_beta_step x with
      | Some x' => Some (x' * y)
      | None =>
          match try_beta_step y with
          | Some y' => Some (x * y')
          | None => None
          end
      end
  | _ => None
  end.

Section try_beta_step.
  Variable Var : Set.
  Variable x : Code Var.
  Eval compute in
    (try_beta_step ((x || (C * I * TOP) o (V * (C * I * TOP)) * x))).
End try_beta_step.

Ltac beta_to x := apply beta_trans with x; auto.

Ltac beta_step_ try_beta_step :=
  match goal with
  | [|- @beta ?v ?x ?y] =>
      match eval compute in (try_beta_step v x) with
      | Some ?z => beta_to z
      | _ => fail
      end
  | _ => fail
  end.

Ltac beta_step := beta_step_ @try_beta_step.

Definition code_div {Var : Set} : Code Var := V * (C * I * TOP).
Lemma beta_div {Var : Set} (x : Code Var) :
  beta (code_div * x) (x || code_div * x * TOP).
Proof.
  unfold code_div.
  beta_step.
  beta_step.
  beta_step.
  apply beta_ap_right. (* FIXME allow variables in beta_step *)
  beta_step.
  beta_step.
Qed.

Definition conv {Var : Set} (x : Code Var) := beta (code_div * x) TOP.

(** ** Substitution and abstraction *)

Fixpoint code_sub {Var Var' : Set}
  (f : Var -> Code Var') (x : Code Var) : Code Var' :=
  match x with
  | code_var v => f v
  | l * r => (code_sub f l) * (code_sub f r)
  | TOP => TOP
  | BOT => BOT
  | J => J
  | I => I
  | K => K
  | B => B
  | C => C
  | S => S
  | Y => Y
  | V => V
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

Lemma beta_sub_left {Var Var' : Set}
  {f g : Var -> Code Var'} (fg : forall v, beta (f v) (g v))
  (x : Code Var) : beta (code_sub f x) (code_sub g x).
Proof.
  induction x; auto.
    compute; auto.
  unfold code_sub; fold (@code_sub Var Var').
  beta_to (code_sub f x1 * code_sub g x2).
Defined.
Hint Resolve beta_sub_left.

Lemma beta_sub_right {Var Var' : Set}
  (f : Var -> Code Var') (x y : Code Var) (xy : beta x y) :
  beta (code_sub f x) (code_sub f y).
Proof.
  induction x; inversion xy; auto.
  (* TODO *)
Admitted.
Hint Resolve beta_sub_right.

Lemma beta_sub {Var Var' : Set}
  {f g : Var -> Code Var'} (fg : forall v, beta (f v) (g v))
  {x y : Code Var} (xy : beta x y) :
  beta (code_sub f x) (code_sub g y).
Proof.
  beta_to (code_sub g x).
Defined.
Hint Resolve beta_sub.

(** Contexts, convergence, and information ordering *)

(** Contexts represent linear functions of code *)
Inductive Context (Var Var' : Set) : Set :=
  Context_intro : (Var -> Code Var') -> Code (option Var') -> Context Var Var'.
Definition context_intro {Var Var' : Set} := Context_intro Var Var'.

Fixpoint context_eval {Var Var' : Set}
  (c : Context Var Var') (x : Code Var) : Code Var' :=
  let (c1, c2) := c in
  let x' := code_sub c1 x in
  let f v := match v with None => x' | Some v' => code_var v' end in
  code_sub f c2.

Notation "c @ x" := (context_eval c x)
  (at level 60, no associativity) : code_scope.
Notation "( c1 , c2 ) @ x" := (context_intro c1 c2 @ x)
  (at level 60, no associativity) : code_scope.

Lemma context_beta_right {Var Var' : Set}
  (c : Context Var Var') (x y : Code Var) (xy : beta x y) :
  beta (c @ x) (c @ y).
Proof.
  (* TODO *)
Admitted.

Definition conv_in {Var Var' : Set}
  (c : Context Var Var') (x : Code Var) : Prop :=
  conv (c @ x).

Definition code_le {Var : Set} (x y : Code Var) : Prop :=
  forall (Var' : Set) (c : Context Var Var'), conv_in c x -> conv_in c y.

Definition context_div {Var Var' : Set}
  (c1 : Var -> Code Var') (c2 : Code (option Var'))
  (x : Code Var) :
  code_div * ((c1, c2) @ x) = (fun v => code_div * c1 v, c2) @ x.
Proof.
  unfold context_eval at 2; simpl.
Admitted.

Lemma code_le_x_top' {Var : Set} (c x : Code Var) :
  beta (c * x) TOP -> beta (c * TOP) TOP.
Proof.
  apply beta_trans; auto.
Qed.

Lemma code_le_x_top {Var : Set} (x : Code Var) : code_le x code_top.
Proof.
  unfold code_le; unfold conv_in; unfold conv; intros Var' c.
  destruct c as [c1 c2].
  repeat rewrite context_div.
  intros Hbeta.
  beta_to ((fun v : Var => code_div * c1 v, c2) @ x).
  apply context_beta_right; auto.
Defined.

Lemma code_le_bot_x' {Var : Set} (c x : Code Var) :
  beta (c * BOT) TOP -> beta (c * x) TOP.
Proof.
  apply beta_trans; auto.
Qed.

Lemma code_le_bot_x {Var : Set} (x : Code Var) : code_le code_bot x.
Proof.
  unfold code_le; unfold conv_in; unfold conv; intros Var' c.
  destruct c as [c1 c2].
  repeat rewrite context_div.
  intros Hbeta.
  beta_to ((fun v : Var => code_div * c1 v, c2) @ BOT).
  apply context_beta_right; auto.
Defined.

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

(** ** Curry's abstraction algorithm *)

Fixpoint code_abs {Var Var' : Set} (b : Var -> option Var') (x : Code Var) :
  Code Var' :=
  match x with
  | code_var v =>
      match b v with
      | None => I
      | Some v' => K * (code_var v')
      end
  | l * r => S * (code_abs b l) * (code_abs b r)
  | TOP => K * TOP
  | BOT => K * BOT
  | J => K * J
  | I => K * I
  | K => K * K
  | B => K * B
  | C => K * C
  | S => K * S
  | Y => K * Y
  | V => K * V
  end.

Lemma abs_sub_beta {Var Var' : Set}
  (b : Var -> option Var') (x : Code Var) (y : Code Var') :
  beta (code_abs b x * y)
       (code_sub (fun v => match b v with None => y
                                        | Some v' => code_var v' end) x).
Proof.
  induction x; simpl; auto.
    case (b v); [intro v'; auto | auto].
  beta_to (code_abs b x1 * y * (code_abs b x2 * y)).
  beta_to
    (code_abs b x1 * y
    * (code_sub (fun v => match b v with None => y
                                       | Some v' => code_var v' end) x2)).
Qed.

Fixpoint code_abs' {Var Var' : Set} (b : Var -> option Var') (x : Code Var) :
  Code Var' :=
  match x with
  | code_var v =>
      match b v with
      | None => I
      | Some v' => K * (code_var v')
      end
  | l * r => 
      match code_abs' b l, code_abs' b r with
      | K * l', I => l'
      | K * l', K * r' => K * (l' * r')
      | K * l', r' => B * l' * r'
      | l', K * r' => C * l' * r'
      | l', r' => S * l' * r'
      end
  | TOP => K * TOP
  | BOT => K * BOT
  | J => K * J
  | I => K * I
  | K => K * K
  | B => K * B
  | C => K * C
  | S => K * S
  | Y => K * Y
  | V => K * V
  end.

Lemma abs_sub_beta' {Var Var' : Set}
  (b : Var -> option Var') (x : Code Var) (y : Code Var') :
  beta (code_abs' b x * y)
       (code_sub (fun v => match b v with None => y
                                        | Some v' => code_var v' end) x).
Proof.
  (* TODO *)
Admitted.

(** Sloppy lambda notation specialized to [Code nat] *)

Definition nat_match (m n : nat) : option nat :=
  if beq_nat m n then None else Some m.

Definition code_lambda (v : Code nat) (x : Code nat) : Code nat :=
  match v with
  | code_var n => code_abs (nat_match n) x
  | _ => code_top (* TODO implement pattern matching here*)
  end.

Notation "\ x , y" := (code_lambda x y)%code : code_scope.
