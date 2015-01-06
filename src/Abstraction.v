Require Import EqNat.
Require Import Notations.
Require Import Codes.

(** * Curry's abstraction algorithm *)

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

Lemma abs_sub_red {Var Var' : Set}
  (b : Var -> option Var') (x : Code Var) (y : Code Var') :
  red (code_abs b x * y)
       (code_sub (fun v => match b v with None => y
                                        | Some v' => code_var v' end) x).
Proof.
  induction x; simpl; auto.
    case (b v); [intro v'; auto | auto].
  red_to (code_abs b x1 * y * (code_abs b x2 * y)).
  red_to
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

Lemma abs_sub_red' {Var Var' : Set}
  (b : Var -> option Var') (x : Code Var) (y : Code Var') :
  red (code_abs' b x * y)
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
