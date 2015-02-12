Require Import Codes.
Require Import Combinators.
Require Import DeBruijn.
Require Import BohmTrees.

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

(* TODO this needs to be changed to get [decompile_compile] to hold *)
Fixpoint decompile {Var : Set} (c : Code Var) : Term Var :=
  match c with
  | TOP%code => TOP
  | BOT%code => BOT
  | I => DeBruijn.I
  | K => DeBruijn.K
  | B => DeBruijn.B
  | C => DeBruijn.C
  | S => DeBruijn.S
  | J => (DeBruijn.I || DeBruijn.I)
  | R => (DeBruijn.I || DeBruijn.I)
  | (x || y)%code => (decompile x || decompile y)
  | (x (+) y)%code => (decompile x (+) decompile y)
  | (x * y)%code => (decompile x * decompile y)
  | code_var v => term_var v
  end.

(* maybe restrict [t] to Bohm trees *)
Lemma decompile_compile (Var : Set) (t : Term Var) : decompile (compile t) = t.
Proof.
  induction t; simpl; auto.
  - rewrite IHt1, IHt2; reflexivity.
  - rewrite IHt1, IHt2; reflexivity.
  - rewrite IHt1, IHt2; clear IHt1 IHt2.
    case_eq t1; auto.
    + admit. (* easy *)
    + admit. (* easy *)
  - admit. (* TODO this is the crucial case *)
Qed.
