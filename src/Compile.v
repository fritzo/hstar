(** * Converting between combinatory algebra and lambda-calculus *)

Require Import Coq.Program.Equality.
Require Import Codes.
Require Import Combinators.
Require Export DeBruijn.

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
      | [ H : compiles_to t _ |- _] =>
        apply H' in H; rewrite H; clear H H'; simpl
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


Definition code_protect {Var : Set} : Code Var -> Code (option' Var) :=
  code_sub (fun v : Var => code_var (Some v)).

Definition term_protect {Var : Set} : Term Var -> Term (option' Var) :=
  term_map (@Some Var).

(* TODO this needs to be changed to get [decompile_compile] to hold,
   at least when restricted to Bohm trees. *)
Fixpoint decompile {Var : Set} (c : Code Var) : Term Var :=
  match c with
  | TOP%code => TOP
  | BOT%code => BOT
  | (J * x * y)%code => decompile x || decompile y
  | (R * x * y)%code => decompile x (+) decompile y
  | I => DeBruijn.I
  | (K * x)%code =>
      let x' := term_protect (decompile x) in
      LAMBDA x'
  | (B * x * y)%code =>
      (* should this be [decompile (term_protect x * v)] ? *)
      let x' := term_protect (decompile x) in
      let y' := term_protect (decompile y) in
      let v := VAR None in
      LAMBDA (x' * (y' * v))
  | (C * x * y)%code =>
      let x' := term_protect (decompile x) in
      let y' := term_protect (decompile y) in
      let v := VAR None in
      LAMBDA (x' * v * y')
  | (S * x * y)%code =>
      let x' := term_protect (decompile x) in
      let y' := term_protect (decompile y) in
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

Inductive decompiles_to {Var : Set} : Code Var -> Term Var -> Prop :=
  | decompiles_to_top : decompiles_to TOP%code TOP
  | decompiles_to_bot : decompiles_to BOT%code BOT
  | decompiles_to_join x x' y y' :
     decompiles_to x x' -> decompiles_to y y' ->
     decompiles_to (J * x * y)%code (x' || y')
  | decompiles_to_rand x x' y y' :
     decompiles_to x x' -> decompiles_to y y' ->
     decompiles_to (R * x * y)%code (x' (+) y')
  | decompiles_to_i : decompiles_to I DeBruijn.I
  | decompiles_to_k1 x x' :
      decompiles_to x x' ->
      let x'' := term_protect x' in
      decompiles_to (K * x)%code (LAMBDA x'')
  | decompiles_to_b2 x x' y y' :
      decompiles_to x x' ->
      decompiles_to y y' ->
      let x'' := term_protect x' in
      let y'' := term_protect y' in
      let v := VAR None in
      decompiles_to (B * x * y)%code (LAMBDA (x'' * (y'' * v)))
  | decompiles_to_c2 x x' y y' :
      decompiles_to x x' ->
      decompiles_to y y' ->
      let x'' := term_protect x' in
      let y'' := term_protect y' in
      let v := VAR None in
      decompiles_to (C * x * y)%code (LAMBDA (x'' * v * y''))
  | decompiles_to_s2 x x' y y' :
      decompiles_to x x' ->
      decompiles_to y y' ->
      let x'' := term_protect x' in
      let y'' := term_protect y' in
      let v := VAR None in
      decompiles_to (S * x * y)%code (LAMBDA (x'' * v * (y'' * v)))
  | decompiles_to_app x x' y y':
      decompiles_to x x' ->
      decompiles_to y y' ->
      decompiles_to (x * y)%code (x' * y')
  | decompiles_to_var v : decompiles_to (code_var v) (term_var v)
  (* these cases never arise as [decompile (compile t)] *)
  | decompiles_to_k : decompiles_to K DeBruijn.K
  | decompiles_to_b : decompiles_to B DeBruijn.B
  | decompiles_to_c : decompiles_to C DeBruijn.C
  | decompiles_to_s : decompiles_to S DeBruijn.S
  | decompiles_to_j : decompiles_to J (DeBruijn.K || DeBruijn.F)
  | decompiles_to_r : decompiles_to R (DeBruijn.K (+) DeBruijn.F)
.
Hint Constructors decompiles_to.

Section decompiles_to_decompile.
  Local Ltac decompiles_to_decompiles :=
    simpl;
    repeat match goal with
    | [ H' : forall c : _, decompiles_to c ?t -> decompile c = ?t |- _] =>
      match goal with
      | [ H : decompiles_to _ t |- _] =>
        apply H' in H; rewrite H; clear H H'; simpl
      end
    end;
    auto.

  Lemma decompiles_to_decompile (Var : Set) (c : Code Var) (t : Term Var) :
    decompiles_to c t <-> decompile c = t.
  Proof.
    split.
    - intro H; induction t; inversion H; decompiles_to_decompiles;
      admit.
    - intro H; dependent induction c;
      try (simpl in H; rewrite <- H; auto; reflexivity).
      admit.
  Qed.
End decompiles_to_decompile.


Lemma compile_app (Var : Set) (x y : Term Var) :
  (compile (x * y) = (compile x) * (compile y))%code.
Proof.
  simpl; reflexivity.
Qed.

Lemma compile_lambda_app (Var : Set) (x : Term (option Var)) (y : Term Var) :
  (compile (lambda_app_sub x y) == code_abs id (compile x) * compile y)%code.
Proof.
  dependent induction x.
  - simpl; code_simpl; reflexivity.
  - simpl; code_simpl; reflexivity.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
Qed.


Section compile_decompile.
  Lemma compile_protect (Var : Set) (t : Term Var) :
    compile (term_protect t) = code_protect (compile t).
  Proof.
    apply compiles_to_compile.
    induction t; try (compute; auto; reflexivity).
    admit.
  Qed.

  Lemma protect_decompile (Var : Set) (c : Code Var) :
    decompile (code_protect c) = term_protect (decompile c).
  Proof.
    apply decompiles_to_decompile.
    admit.
  Qed.

  Lemma code_abs_protect (Var : Set) (c : Code Var) :
    code_abs id (code_protect c) = (K * c)%code.
  Proof.
    induction c; try (simpl; auto; reflexivity).
    admit. (* TODO this should be true *)
  Qed.

  Lemma compile_decompile (Var : Set) (c : Code Var) :
    (compile (decompile c) == c)%code.
  Proof.
    induction c; simpl; auto.
    - case_eq c1; intros; try (simpl; auto; reflexivity).
      + admit.
      + simpl; rewrite IHc2; beta_eta.
      + simpl; rewrite IHc2; beta_eta.
      + simpl; rewrite compile_protect.
        rewrite code_abs_protect.
        monotonicity; assumption.
    - beta_eta.
    - beta_eta.
  Qed.
End compile_decompile.
