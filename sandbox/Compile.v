Require Import Codes.
Require Import Combinators.
Require Import DeBruijn.
Require Import BohmTrees.

Definition protect {Var : Set} : Term Var -> Term (option' Var) :=
  term_map (@Some Var).

Fixpoint compile {Var : Set} (t : Term Var) : Code Var :=
  match t with
  | TOP%term => TOP%code
  | BOT%term => BOT%code
  | x || y => (compile x || compile y)%code
  | x (+) y => (compile x (+) compile y)%code
  | x * y => (compile x * compile y)%code
  | term_var v => code_var v
  | term_lambda x => code_abs id (compile x)
  end.

(* TODO this needs to be changed to get [decompile_compile] to hold,
   at least when restricted to Bohm trees. *)
Fixpoint decompile {Var : Set} (c : Code Var) : Term Var :=
  match c with
  | TOP%code => TOP
  | BOT%code => BOT
  | (J * x * y)%code => decompile x || decompile y
  | (R * x * y)%code => decompile x (+) decompile y
  | I => 
      let v := VAR None in
      LAMBDA v
  | (K * x)%code =>
      let x' := protect (decompile x) in
      LAMBDA x'
  | (B * x * y)%code =>
      (* should this be [decompile (protect x * v)] ? *)
      let x' := protect (decompile x) in
      let y' := protect (decompile y) in
      let v := VAR None in
      LAMBDA (x' * (y' * v))
  | (C * x * y)%code =>
      let x' := protect (decompile x) in
      let y' := protect (decompile y) in
      let v := VAR None in
      LAMBDA (x' * v * y')
  | (S * x * y)%code =>
      let x' := protect (decompile x) in
      let y' := protect (decompile y) in
      let v := VAR None in
      LAMBDA (x' * v * y')
  | (x * y)%code => (decompile x * decompile y)
  | code_var v => term_var v
  (* these cases never arise as [decompile (compile t)] *)
  | K => DeBruijn.K
  | B => DeBruijn.B
  | C => DeBruijn.C
  | S => DeBruijn.S
  | J => DeBruijn.K || DeBruijn.F
  | R => DeBruijn.K (+) DeBruijn.F
  end.

(* maybe restrict [t] to Bohm trees *)
Lemma decompile_compile (Var : Set) (t : Term Var) : decompile (compile t) = t.
Proof.
  induction t; simpl; auto.
  - rewrite IHt1, IHt2; reflexivity.
  - rewrite IHt1, IHt2; reflexivity.
  - rewrite IHt1, IHt2; clear IHt1 IHt2.
    case_eq t1; simpl; auto.
    + intros; case_eq (compile t); auto;
      admit.
    + intros; case_eq (code_abs id (compile t)); intros; subst; auto;
      admit.
  - admit.
Qed.
