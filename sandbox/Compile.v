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

Inductive compiles_to {Var : Set} : Term Var -> Code Var -> Prop :=
  | compiles_to_top : compiles_to TOP%term TOP%code
  | compiles_to_bot : compiles_to BOT%term BOT%code
  | compiles_to_join x x' y y' :
     compiles_to x x' -> compiles_to y y' ->
     compiles_to (x || y) (x' || y')%code
  | compiles_to_rand x x' y y' :
     compiles_to x x' -> compiles_to y y' ->
     compiles_to (x (+) y) (x' (+) y')%code
  | compiles_to_app x x' y y' :
     compiles_to x x' -> compiles_to y y' ->
     compiles_to (x * y) (x' * y')%code
  | compiles_to_var v : compiles_to (term_var v) (code_var v)
  | compiles_to_lambda x x' :
      @compiles_to (option Var) x x' ->
      compiles_to (term_lambda x) (code_abs id x')
.
Hint Constructors compiles_to.

Section compiles_to_compile.
  Local Ltac compiles_to_compiles :=
    simpl;
    repeat match goal with
    | [ H' : forall c : _, compiles_to ?t c -> compile ?t = c |- _] =>
      match goal with
      | [ H : compiles_to ?t ?c' |- _] =>
        apply H' in H; rewrite H; clear H; simpl
      end
    end;
    auto.

  Lemma compiles_to_compile (Var : Set) (t : Term Var) (c : Code Var) :
    compiles_to t c <-> compile t = c.
  Proof.
    split.
    - intro H; induction t; inversion H; compiles_to_compiles.
    - intro H; induction t; simpl in H; rewrite <- H; auto.
  Qed.
End compiles_to_compile.


Definition protect {Var : Set} : Term Var -> Term (option' Var) :=
  term_map (@Some Var).

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
      LAMBDA (x' * v * (y' * v))
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


Section decompile_compile.
  Local Ltac decompile_compile :=
    simpl;
    repeat match goal with
    | [H : decompile (compile ?x) = ?x |- _] => rewrite H; clear H; simpl
    end.

  Lemma decompile_compile_normal (Var : Set) (t : Term Var) :
   normal t -> decompile (compile t) = t.
  Proof.
    intro Hn; induction Hn; decompile_compile; auto.
    - case_eq (compile x); intros; try (compute; reflexivity);
      admit.
    - admit.
  Qed.

  Lemma decompile_compile (Var : Set) (t : Term Var) :
    decompile (compile t) = t.
  Proof.
    induction t; decompile_compile; auto.
    - case_eq (compile t1); simpl; auto.
      + intros; case_eq c; auto;
        admit.
      + intros.
        admit.
    - admit.
  Qed.
End decompile_compile.
