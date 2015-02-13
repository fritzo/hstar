(** * Lambda calculus parametric de Bruijn terms *)

(**
  We use the parametric de Bruijn convention of
  https://coq.inria.fr/cocorico/UntypedLambdaTerms
  and earlier Bird and Patterson \cite{bird1999bruijn}.
  See also Capretta and Felty \cite{capretta2007combining}.
*)

Definition Succ := S%nat.  (* an alias for later *)

Require Import Coq.Program.Basics.
Require Import Coq.Program.Equality.
Require Import Coq.Setoids.Setoid.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Export Notations.


(* ------------------------------------------------------------------------ *)
(** ** Terms *)

Inductive Term {Var : Set} : Set :=
  | term_top : Term
  | term_bot : Term
  | term_join : Term -> Term -> Term
  | term_rand : Term -> Term -> Term
  | term_app : Term -> Term -> Term
  | term_var : Var -> Term
  | term_lambda : @Term (option Var) -> Term.
Arguments Term : default implicits.
Hint Constructors Term.
Definition Closed := Term Empty_set.

Notation "'TOP'" := term_top : term_scope.
Notation "'BOT'" := term_bot : term_scope.
Notation "'JOIN'" := term_join : term_scope.
Notation "'RAND'" := term_rand : term_scope.
Notation "'APP'" := term_app : term_scope.
Notation "'VAR'" := term_var : term_scope.
Notation "'LAMBDA'" := term_lambda : term_scope.

Open Scope term_scope.
Delimit Scope term_scope with term.
Bind Scope term_scope with Term.

Notation "x * y" := (APP x y) : term_scope.
Notation "x || y" := (JOIN x y) : term_scope.
Notation "x (+) y" := (RAND x y) : term_scope.


(* ------------------------------------------------------------------------ *)
(** ** Lambda notation *)

Fixpoint iter {a : Type} (z : a) (s : a -> a) (n : nat) {struct n} :=
  match n with
  | 0 => z
  | Succ n' => s (iter z s n')
  end.

Fixpoint iter_dep
  {tz : Set} {ts : Set -> Set}
  (x : tz) (f : forall t : Set, t -> ts t) (n : nat) {struct n} :=
  match n return iter tz ts n with
  | 0 => x
  | Succ n' => f _ (iter_dep x f n')
  end.

Fixpoint iter_depT
  {tz : Type} {ts : Type -> Type}
  (x : tz) (f : forall t : Type, t -> ts t) (n : nat) {struct n} :=
  match n return iter tz ts n with
  | 0 => x
  | Succ n' => f _ (iter_depT x f n')
  end.

(* restrict [option] to [Set] level *)
Definition option' (a : Set) : Set := option a.
Definition Some' (a : Set) (x : a) : option' a := Some x.
Definition None' {a : Set} : option' a := None.

Definition option_ (n : nat) (v : Set) := iter v option' n.
Definition Some_ (n : nat) (v : Set) := iter_depT v Some n.
Definition lam_ {Var : Set} (n : nat) (x : Term (option_ n Var)) :=
  iter_dep x (@term_var) n.
(*
Definition var_ {Var : Set} (n : nat) : Term (option_ n Var) :=
  @VAR (option_ n Var) (iter_dep (@None' Var) Some' n).
*)

Section I.
  Definition v0 {Var : Set} : Term (option_ 1 Var) := VAR None.
  Definition v1 {Var : Set} : Term (option_ 2 Var) := VAR (Some None).
  Definition v2 {Var : Set} : Term (option_ 3 Var) := VAR (Some (Some None)).
  Context {Var : Set}.

  Definition I : Term Var := Eval compute in
    LAMBDA v0.
  Definition K : Term Var := Eval compute in
    LAMBDA (LAMBDA (VAR (Some None))).
  Definition F : Term Var := Eval compute in
    LAMBDA (LAMBDA (VAR None)).
  Definition B : Term Var := Eval compute in
    LAMBDA (LAMBDA (LAMBDA (v2 * (v1 * v0)))).
  Definition C : Term Var := Eval compute in
    LAMBDA (LAMBDA (LAMBDA (v2 * v0 * v1))).
  Definition S : Term Var := Eval compute in
    LAMBDA (LAMBDA (LAMBDA (v2 * v0 * (v1 * v0)))).
End I.
Print S.  (* Ugly! *)

Notation "x 'o' y" := (B * x * y) : term_scope.

(* TODO figure out how to use lambda notation
Notation "\ x , y" := (LAMBDA) : code_scope.
*)


(* ------------------------------------------------------------------------ *)
(** ** Substitution *)

(* adapted from https://coq.inria.fr/cocorico/UntypedLambdaTerms *)

Lemma ext_respectful
  (a b : Type) (f g : a -> b) (r : relation b) (fg : forall x, r (f x) (g x)) :
  respectful eq r f g.
Proof.
  intros x x' xx'; rewrite xx'; auto.
Qed.

Instance option_map_proper (Var Var' : Set) :
  Proper ((eq ==> eq) ==> eq ==> eq) (@option_map Var Var').
Proof.
  intros f f' ff' v v' vv'; compute in ff'; rewrite <- vv'; clear v' vv'.
  case_eq v; intro v0; intros; simpl; auto.
  assert (f v0 = f' v0) as eq; [apply ff' | rewrite eq]; auto.
Qed.

Fixpoint term_map {Var Var' : Set} (f : Var -> Var') (x : Term Var) :
  Term Var' :=
  match x with
  | TOP => TOP
  | BOT => BOT
  | x1 || x2 => term_map f x1 || term_map f x2
  | x1 (+) x2 => term_map f x1 (+) term_map f x2
  | x1 * x2 => term_map f x1 * term_map f x2
  | term_var x => VAR (f x)
  | term_lambda x1 => LAMBDA (term_map (option_map f) x1)
  end.

Instance term_map_proper (Var Var' : Set) :
  Proper ((eq ==> eq) ==> eq ==> eq) (@term_map Var Var').
Proof.
  intros f f' ff' x x' xx'; compute in ff'; rewrite <- xx'; clear x' xx'.
  revert Var' f f' ff'; induction x; intros Var' f f' ff'; simpl; auto.
  - rewrite (IHx1 Var' f f'), (IHx2 Var' f f'); auto.
  - rewrite (IHx1 Var' f f'), (IHx2 Var' f f'); auto.
  - rewrite (IHx1 Var' f f'), (IHx2 Var' f f'); auto.
  - rewrite (ff' v v); auto.
  - rewrite (IHx (option Var') (option_map f) (option_map f')); auto.
    apply option_map_proper; auto.
Qed.

Definition some_sub
  {Var Var' : Set} (f : Var -> Term Var') (v : option Var) :
  Term (option Var') :=
  match v with
  | None => VAR None
  | Some v' => term_map (@Some Var') (f v')
  end.

Instance some_sub_proper (Var Var' : Set) :
  Proper ((eq ==> eq) ==> eq ==> eq) (@some_sub Var Var').
Proof.
  intros f f' ff' v v' vv'; compute in ff'; rewrite <- vv'; clear v' vv'.
  case_eq v; intro v0; intros; simpl; auto.
  assert (f v0 = f' v0) as eq; [apply ff' | rewrite eq]; auto.
Qed.

Fixpoint term_sub {Var Var' : Set} (f : Var -> Term Var') (x : Term Var) :
  Term Var' :=
  match x with
  | TOP => TOP
  | BOT => BOT
  | x1 || x2 => term_sub f x1 || term_sub f x2
  | x1 (+) x2 => term_sub f x1 (+) term_sub f x2
  | x1 * x2 => term_sub f x1 * term_sub f x2
  | term_var v => f v
  | term_lambda x1 => LAMBDA (term_sub (some_sub f) x1)
  end.

Instance term_sub_proper (Var Var' : Set) :
  Proper ((eq ==> eq) ==> eq ==> eq) (@term_sub Var Var').
Proof.
  intros f f' ff'; compute in ff'.
  intros x x' xx'; rewrite <- xx'; clear x' xx'.
  revert Var' f f' ff'; induction x; intros Var' f f' ff'; auto.
  - simpl; rewrite (IHx1 Var' f f'), (IHx2 Var' f f'); auto.
  - simpl; rewrite (IHx1 Var' f f'), (IHx2 Var' f f'); auto.
  - simpl; rewrite (IHx1 Var' f f'), (IHx2 Var' f f'); auto.
  - compute; auto.
  - simpl; rewrite (IHx _ (some_sub f) (some_sub f')); clear IHx; auto.
    intros v v' vv'; rewrite <- vv'; clear v' vv' x.
    apply some_sub_proper; auto.
Qed.

Notation "x @ f" := (term_sub f x) : term_scope.

Definition sub_top {Var : Set} (v : Var) : Closed := TOP.
Definition close {Var : Set} : Term Var -> Closed := term_sub sub_top.

Definition sub_empty {Var : Set} (v : Empty_set) : Var := match v with end.
Definition open (Var : Set) : Closed -> Term Var := term_map sub_empty.

Tactic Notation "term_simpl" := autorewrite with term_simpl.
Tactic Notation "term_simpl" "in" hyp(H) := autorewrite with term_simpl in H.

Lemma var_monad_unit_right (Var : Set) (x : Term Var) : x @ VAR = x.
Proof.
  induction x; auto; simpl;
  repeat
    match goal with
    | [H : _ @ VAR = _ |- _] => rewrite H; clear H
    end;
  try reflexivity.
  admit.
Qed.
Hint Rewrite var_monad_unit_right : term_simpl.

Lemma var_monad_unit_left (Var Var' : Set) (f : Var -> Term Var') x :
  (VAR x) @ f = f x.
Proof.
  compute; auto.
Qed.
Hint Rewrite var_monad_unit_left : term_simpl.

Lemma term_sub_ap (Var Var' : Set) (x y : Term Var) (f : Var -> Term Var') :
  (x * y @ f) = (x @ f) * (y @ f).
Proof.
  simpl; auto.
Qed.
Hint Rewrite term_sub_ap : term_simpl.

Lemma term_sub_join (Var Var' : Set) (x y : Term Var) (f : Var -> Term Var') :
  (x || y @ f) = (x @ f) || (y @ f).
Proof.
  simpl; auto.
Qed.
Hint Rewrite term_sub_join : term_simpl.

Lemma term_sub_rand (Var Var' : Set) (x y : Term Var) (f : Var -> Term Var') :
  (x (+) y @ f) = (x @ f) (+) (y @ f).
Proof.
  simpl; auto.
Qed.
Hint Rewrite term_sub_rand : term_simpl.

Lemma term_sub_lambda
  (Var Var' : Set) (x : Term (option Var)) (f : Var -> Term Var') :
  (LAMBDA x @ f) = LAMBDA (x @ some_sub f).
Proof.
  simpl; auto.
Qed.
Hint Rewrite term_sub_lambda : term_simpl.

Lemma var_monad_assoc
  (Var Var' Var'' : Set)
  (f : Var -> Term Var')
  (g : Var' -> Term Var'')
  (x : Term Var) :
  (x @ f) @ g = x @ (fun v => (f v) @ g).
Proof.
  revert Var' Var'' f g; induction x; intros Var' Var'' f g; auto.
  - term_simpl; rewrite IHx1; rewrite IHx2; auto.
  - term_simpl; rewrite IHx1; rewrite IHx2; auto.
  - term_simpl; rewrite IHx1; rewrite IHx2; auto.
  - term_simpl; rewrite IHx; simpl; auto.
    admit.
Qed.
Hint Rewrite var_monad_assoc : term_simpl.

Lemma close_idempotent (Var : Set) (x : Term Var) : close (close x) = close x.
Proof.
  compute; term_simpl; induction x; auto.
Qed.
Hint Rewrite close_idempotent : beta_simpl.
Hint Rewrite close_idempotent : term_simpl.

Lemma close_closed (x : Closed) : close x = x.
Proof.
  unfold Closed in x; unfold close, sub_top.
  dependent induction x; term_simpl;
  match goal with [v : Empty_set |- _] => destruct v | _ => idtac end; auto.
  - rewrite IHx1; rewrite IHx2; reflexivity.
  - rewrite IHx1; rewrite IHx2; reflexivity.
  - rewrite IHx1; rewrite IHx2; reflexivity.
  - clear IHx.
    set (f := fun _ : Empty_set => TOP).
    rewrite <- var_monad_unit_right; simpl.
    assert (forall v, f v = VAR v) as eq; [intro v; case v|].
    apply ext_respectful in eq.
    apply some_sub_proper in eq.
    apply term_sub_proper in eq.
    unfold respectful in eq.
    rewrite (eq x x); auto.
Qed.
Hint Rewrite close_closed : beta_simpl.
Hint Rewrite close_closed : term_simpl.

Lemma open_close
  (Var : Set) (f : Var -> Term Empty_set) (x : Term Empty_set) :
  (open Var x) @ f = x.
Proof.
  unfold open.
  revert Var f; dependent induction x; intros Var f; simpl; auto.
  - rewrite (IHx1 Var f), (IHx2 Var f); auto.
  - rewrite (IHx1 Var f), (IHx2 Var f); auto.
  - rewrite (IHx1 Var f), (IHx2 Var f); auto.
  - case v.
  - admit.
Qed.

Lemma term_sub_ext (Var Var' : Set)
  (f g : Var -> Term Var') (fg : forall v, f v = g v) x :
  x @ f = x @ g.
Proof.
  revert Var' f g fg; induction x; intros Var' f g fg; simpl; auto.
  - rewrite (IHx1 Var' f g), (IHx2 Var' f g); auto.
  - rewrite (IHx1 Var' f g), (IHx2 Var' f g); auto.
  - rewrite (IHx1 Var' f g), (IHx2 Var' f g); auto.
  - rewrite (IHx (option Var') (some_sub f) (some_sub g)); auto.
    apply ext_respectful in fg.
    intros; apply (some_sub_proper Var _ f g fg); auto.
Qed.


(* ------------------------------------------------------------------------ *)
(** ** Reduction relations *)

Inductive star {Var : Set} (r : relation (Term Var)) : relation (Term Var) :=
  | star_step {x y} : r x y -> star r x y
  | star_refl {x} : star r x x
  | star_trans {x} y {z} : star r x y -> star r y z -> star r x z.
Hint Constructors star.

Inductive weak_star
  {Var : Set} (r : relation (Term Var)) : relation (Term Var) :=
  | weak_star_refl {x} : weak_star r x x
  | weak_star_trans {x} y {z} : r x y -> weak_star r y z -> weak_star r x z.
Hint Constructors weak_star.

Lemma weaken_star (Var : Set) (r : relation (Term Var)) (x y : Term Var) :
  star r x y <-> weak_star r x y.
Proof.
  split; intro H; induction H; eauto.
  clear H H0; induction IHstar1; auto.
  apply weak_star_trans with y; auto.
Qed.

Lemma weak_star_flip (Var : Set) (r : relation (Term Var)) (x y : Term Var) :
  weak_star (flip r) x y <-> weak_star r y x.
Proof.
  repeat rewrite <- weaken_star.
  split; intro H; induction H; eauto.
Qed.


Inductive probe {Var : Set} : relation (Term Var) :=
  | probe_refl {x} : probe x x
  | probe_trans {x} y {z} : probe x y -> probe y z -> probe x z
  | probe_top {x} : probe x (x * TOP).
Hint Constructors probe.

Inductive probe_step {Var : Set} : relation (Term Var) :=
  | probe_step_top {x} : probe_step x (x * TOP).
Hint Constructors probe_step.

Lemma weaken_probe (Var : Set) (x y : Term Var) :
  probe x y <-> weak_star probe_step x y.
Proof.
  rewrite <- weaken_star.
  split; intro H; induction H; eauto.
  inversion H; auto.
Qed.

Definition none_sub {Var : Set} (x : Term Var) (v : option Var) : Term Var :=
  match v with
  | None => x
  | Some v' => VAR v'
  end.

Definition lambda_app_sub {Var : Set} (x : Term (option Var)) (y : Term Var) :
  Term Var := x @ (none_sub y).

Inductive beta {Var : Set} : relation (Term Var) :=
  | beta_refl {x} : beta x x
  | beta_trans {x} y {z} : beta x y -> beta y z -> beta x z
  | beta_app_left {x x' y} : beta x x' -> beta (x * y) (x' * y)
  | beta_app_right {x y y'} : beta y y' -> beta (x * y) (x * y')
  | beta_join_left {x x' y} : beta x x' -> beta (x || y) (x' || y)
  | beta_join_right {x y y'} : beta y y' -> beta (x || y) (x || y')
  | beta_rand_left {x x' y} : beta x x' -> beta (x (+) y) (x' (+) y)
  | beta_rand_right {x y y'} : beta y y' -> beta (x (+) y) (x (+) y')
  | beta_lambda {x x'} :
      @beta (option Var) x x' -> beta (LAMBDA x) (LAMBDA x')
  | beta_sub {x y} : beta (LAMBDA x * y) (lambda_app_sub x y)
  | beta_j_ap {x y z} : beta ((x || y) * z) (x * z || y * z)
  | beta_r_ap {x y z} : beta ((x (+) y) * z) (x * z (+) y * z)
  | beta_r_idem {x} : beta (x (+) x) x
  | beta_r_sym {x y} : beta (x (+) y) (y (+) x)
  | beta_r_sym_sym {w x y z} :
      beta ((w(+)x) (+) (y(+)z)) ((x(+)y) (+) (z(+)w)).
Hint Constructors beta.

Inductive beta_step {Var : Set} : relation (Term Var) :=
  | beta_step_app_left {x x' y} : beta_step x x' -> beta_step (x * y) (x' * y)
  | beta_step_app_right {x y y'} : beta_step y y' -> beta_step (x * y) (x * y')
  | beta_step_join_left {x x' y} :
      beta_step x x' -> beta_step (x || y) (x' || y)
  | beta_step_join_right {x y y'} :
      beta_step y y' -> beta_step (x || y) (x || y')
  | beta_step_rand_left {x x' y} :
      beta_step x x' -> beta_step (x (+) y) (x' (+) y)
  | beta_step_rand_right {x y y'} :
      beta_step y y' -> beta_step (x (+) y) (x (+) y')
  | beta_step_lambda {x x'} :
      @beta_step (option Var) x x' -> beta_step (LAMBDA x) (LAMBDA x')
  | beta_step_sub {x y} : beta_step (LAMBDA x * y) (lambda_app_sub x y)
  | beta_step_j_ap {x y z} : beta_step ((x || y) * z) (x * z || y * z)
  | beta_step_r_ap {x y z} : beta_step ((x (+) y) * z) (x * z (+) y * z)
  | beta_step_r_idem {x} : beta_step (x (+) x) x
  | beta_step_r_sym {x y} : beta_step (x (+) y) (y (+) x)
  | beta_step_r_sym_sym {w x y z} :
      beta_step ((w(+)x) (+) (y(+)z)) ((x(+)y) (+) (z(+)w)).
Hint Constructors beta_step.

Lemma weaken_beta (Var : Set) (x y : Term Var) :
  beta x y <-> weak_star beta_step x y.
Proof.
  rewrite <- weaken_star.
  split; intro H; induction H; eauto;
  match goal with
  | [IH : star _ _ _ |- star _ _ _ ] => clear H; induction IH; eauto
  | _ => induction H; auto
  end.
Qed.


Inductive pi {Var : Set} : relation (Term Var) :=
  | pi_refl {x} : pi x x
  | pi_trans {x} y {z} : pi x y -> pi y z -> pi x z
  | pi_app_left {x x' y} : pi x x' -> pi (x * y) (x' * y)
  | pi_app_right {x y y'} : pi y y' -> pi (x * y) (x * y')
  | pi_join_left {x x' y} : pi x x' -> pi (x || y) (x' || y)
  | pi_join_right {x y y'} : pi y y' -> pi (x || y) (x || y')
  | pi_rand_left {x x' y} : pi x x' -> pi (x (+) y) (x' (+) y)
  | pi_rand_right {x y y'} : pi y y' -> pi (x (+) y) (x (+) y')
  | pi_lambda {x x'} : @pi (option Var) x x' -> pi (LAMBDA x) (LAMBDA x')
  | pi_sub {x y} : pi (LAMBDA x * y) (lambda_app_sub x y)
  | pi_j_ap {x y z} : pi ((x || y) * z) (x * z || y * z)
  | pi_r_ap {x y z} : pi ((x (+) y) * z) (x * z (+) y * z)
  | pi_r_idem {x} : pi (x (+) x) x
  | pi_r_sym {x y} : pi (x (+) y) (y (+) x)
  | pi_r_sym_sym {w x y z} :
      pi ((w(+)x) (+) (y(+)z)) ((x(+)y) (+) (z(+)w))
  | pi_top x : pi TOP x
  | pi_bot x : pi x BOT
  | pi_j_left {x y} : pi (x || y) x
  | pi_j_right {x y} : pi (x || y) y.
Hint Constructors pi.

Inductive pi_step {Var : Set} : relation (Term Var) :=
  | pi_step_app_left {x x' y} : pi_step x x' -> pi_step (x * y) (x' * y)
  | pi_step_app_right {x y y'} : pi_step y y' -> pi_step (x * y) (x * y')
  | pi_step_join_left {x x' y} : pi_step x x' -> pi_step (x || y) (x' || y)
  | pi_step_join_right {x y y'} : pi_step y y' -> pi_step (x || y) (x || y')
  | pi_step_rand_left {x x' y} : pi_step x x' -> pi_step (x (+) y) (x' (+) y)
  | pi_step_rand_right {x y y'} : pi_step y y' -> pi_step (x (+) y) (x (+) y')
  | pi_step_lambda {x x'} :
      @pi_step (option Var) x x' -> pi_step (LAMBDA x) (LAMBDA x')
  | pi_step_sub {x y} : pi_step (LAMBDA x * y) (lambda_app_sub x y)
  | pi_step_j_ap {x y z} : pi_step ((x || y) * z) (x * z || y * z)
  | pi_step_r_ap {x y z} : pi_step ((x (+) y) * z) (x * z (+) y * z)
  | pi_step_r_idem {x} : pi_step (x (+) x) x
  | pi_step_r_sym {x y} : pi_step (x (+) y) (y (+) x)
  | pi_step_r_sym_sym {w x y z} :
      pi_step ((w(+)x) (+) (y(+)z)) ((x(+)y) (+) (z(+)w))
  | pi_step_top x : pi_step TOP x
  | pi_step_bot x : pi_step x BOT
  | pi_step_j_left {x y} : pi_step (x || y) x
  | pi_step_j_right {x y} : pi_step (x || y) y.
Hint Constructors pi_step.

Lemma weaken_pi (Var : Set) (x y : Term Var) :
  pi x y <-> weak_star pi_step x y.
Proof.
  rewrite <- weaken_star.
  split; intro H; induction H; eauto;
  match goal with
  | [IH : star _ _ _ |- star _ _ _ ] => clear H; induction IH; eauto
  | _ => induction H; auto
  end.
Qed.


Hint Rewrite @beta_j_ap @beta_r_ap @beta_r_idem : beta_safe.
Hint Rewrite @beta_sub : beta_unsafe.

Tactic Notation "beta_simpl" :=
  autorewrite with term_simpl beta_safe.
Tactic Notation "beta_simpl" "in" hyp(H) :=
  autorewrite with term_simpl beta_safe in H.
Tactic Notation "beta_reduce" :=
  autorewrite with term_simpl beta_safe beta_unsafe.
Tactic Notation "beta_reduce" "in" hyp(H) :=
  autorewrite with term_simpl beta_safe beta_unsafe in H.

(** To avoid nontermination in [beta_reduce],
    we provide a mechanism to "freeze" terms during reduction. *)
Tactic Notation "freeze" reference(c) "in" tactic(tac) :=
  let v := fresh "v" in
  let H := fresh "Hv" in
  assert (exists v, c=v) as H;
  [ exists c; reflexivity
  | destruct H as [v H]; rewrite H; tac; destruct H].


Class Commuting (Var : Set) (r s : relation (Term Var)) :=
  commuting : forall x y z, r x y -> s y z -> exists y', s x y' /\ r y' z.

Tactic Notation
  "commute" ident(x) ident(y) ident(z) constr(xy) constr(yz)
  "as" ident(w) :=
  let xy := fresh x y in
  let yx := fresh y x in
  let yz := fresh y z in
  let zy := fresh z y in
  let xw := fresh x w in
  let wz := fresh w z in
  let H := fresh in
  match type of xy with
    | ?r y x => assert (flip r x y) as xy; [unfold flip; assumption | idtac]
    | ?r x y => idtac
  end;
  match type of yz with
    | ?r z y => assert (flip r y z) as yz; [unfold flip; assumption | idtac]
    | ?r y z => idtac
  end;
  set (H := commuting x y z xy yz);
  destruct H as [w [xw wz]];
  try unfold flip in xw, wz.

Lemma weaken_commuting (Var : Set) (r s r' s' : relation (Term Var)) :
  (forall (x y : Term Var), r x y <-> weak_star r' x y) ->
  (forall (x y : Term Var), s x y <-> weak_star s' x y) ->
  (forall x y z, r' x y -> s' y z -> exists y', s x y' /\ r y' z) ->
  Commuting Var r s.
Proof.
  intros Hr Hs Hweak x y z rxy syz.
  rewrite Hr in rxy.
  rewrite Hs in syz.
  induction rxy; induction syz; eauto.
  - exists x; rewrite Hr, Hs; auto.
  - exists z; rewrite Hr, Hs; split; auto.
    apply weak_star_trans with y; auto.
  - exists x; rewrite Hr, Hs; split; auto.
    apply weak_star_trans with y; auto.
  - admit. (* TODO also assume r == star r and s == star s,
              then use strong induction *)
Qed.


Instance probe_reflexive (Var : Set) : Reflexive (@probe Var).
Proof.
  auto.
Qed.

Instance probe_transitive (Var : Set) : Transitive (@probe Var).
Proof.
  intros x y z; apply probe_trans.
Qed.

Instance probe_preorder (Var : Set) : PreOrder (@probe Var).
Proof.
  split; [apply probe_reflexive | apply probe_transitive].
Qed.

Lemma probe_step_probe (Var : Set) (x y : Term Var) :
  probe_step x y -> probe x y.
Proof.
  intro H; inversion H; auto.
Qed.

Ltac simpl_probe_step :=
  repeat
  match goal with
    | [H : probe_step _ _ |- _] => destruct H
  (*
    | [|- probe ?x ?y] => rewrite weaken_probe
    | [H : star probe_step _ _ |- _] => induction H
  *)
    | [H : probe_step ?x ?x -> _ |- _] => clear H
  end;
  eauto.

Instance commuting_flip_probe_probe (Var : Set) :
  Commuting Var (flip probe) probe.
Proof.
  apply (weaken_commuting _ _ _ (flip probe_step) probe_step); auto.
  - intros x y; rewrite weak_star_flip; compute; apply weaken_probe.
  - apply weaken_probe.
  - unfold flip; intros x y z xy yz.
    induction xy; induction yz; eauto.
Qed.


Instance beta_reflexive (Var : Set) : Reflexive (@beta Var).
Proof.
  auto.
Qed.

Instance beta_transitive (Var : Set) : Transitive (@beta Var).
Proof.
  intros x y z; apply beta_trans.
Qed.

Instance beta_preorder (Var : Set) : PreOrder (@beta Var).
Proof.
  split; [apply beta_reflexive | apply beta_transitive].
Qed.

Instance beta_step_subrelation (Var : Set) :
  (@subrelation (Term Var)) beta_step beta.
Proof.
  intros x y H; induction H; eauto.
Qed.

Instance APP_beta (Var : Set) :
  Proper (beta ==> beta ==> beta) (@term_app Var).
Proof.
  intros x x' Hx y y' Hy; transitivity (x * y'); auto.
Qed.

Ltac simpl_beta_step :=
  (* repeat *)
  match goal with
    | [H : beta_step _ _ |- _] => induction H
    | [H : beta_step ?x ?x -> _ |- _] => clear H
  end.

Lemma beta_step_beta (Var : Set) (x y : Term Var) :
  beta_step x y -> beta x y.
Proof.
  intro H; induction H; auto.
Qed.

Instance commuting_flip_beta_beta (Var : Set) : Commuting Var (flip beta) beta.
Proof.
  apply (weaken_commuting _ _ _ (flip beta_step) beta_step); auto.
  - intros x y; rewrite weak_star_flip; compute; apply weaken_beta.
  - apply weaken_beta.
  - compute; intros x y z xy yz.
    (* TODO try induction over just one variable,
       mapping beta to beta.
       The only problem is with steps that are the same (use refl)
       and in beta_r_ when redexes intersect.
       Try to write a tactic matching against beta constructors. *)
    (* OLD
    induction xy; induction yz; auto.
    *)
Admitted. 

Instance commuting_flip_beta_probe (Var : Set) :
  Commuting Var (flip beta) probe.
Proof.
  apply (weaken_commuting _ _ _ (flip beta_step) probe_step); auto.
  - intros x y; rewrite weak_star_flip; compute; apply weaken_beta.
  - apply weaken_probe.
  - compute; intros x y z xy yz.
    destruct yz.
    exists (x * TOP); repeat split; auto.
    apply (@weak_star_trans _ _ x0 x x) in xy; auto.
    rewrite <- weaken_beta in xy; auto.
Qed.

Instance commuting_beta_probe (Var : Set) : Commuting Var beta probe.
Proof.
  apply (weaken_commuting _ _ _ beta_step probe_step); auto.
  - apply weaken_beta.
  - apply weaken_probe.
  - compute; intros x y z xy yz; destruct yz; exists (x * TOP); split; auto.
    rewrite xy; reflexivity.
Qed.


Instance pi_reflexive (Var : Set) : Reflexive (@pi Var).
Proof.
  auto.
Qed.

Instance pi_transitive (Var : Set) : Transitive (@pi Var).
Proof.
  intros x y z; apply pi_trans.
Qed.

Instance pi_preorder (Var : Set) : PreOrder (@pi Var).
Proof.
  split; [apply pi_reflexive | apply pi_transitive].
Qed.

Instance pi_step_pi_subrelation (Var : Set) :
  (@subrelation (Term Var)) pi_step pi.
Proof.
  intros x y H; induction H; eauto.
Qed.

Instance beta_step_pi_subrelation (Var : Set) :
  (@subrelation (Term Var)) beta_step pi.
Proof.
  intros x y H; induction H; eauto.
Qed.

Instance beta_pi_subrelation (Var : Set) : (@subrelation (Term Var)) beta pi.
Proof.
  intros x y Hb; induction Hb; eauto.
Qed.

Instance pi_proper_beta (Var : Set) : Proper (beta --> beta ++> impl) (@pi Var).
Proof.
  intros x x' xx' y y' yy' Hp; compute in yy'.
  apply beta_pi_subrelation in xx'; rewrite xx'.
  apply beta_pi_subrelation in yy'; rewrite <- yy'.
  auto.
Qed.

Instance APP_pi (Var : Set) :
  Proper (pi ==> pi ==> pi) (@term_app Var).
Proof.
  intros x x' Hx y y' Hy; transitivity (x * y'); auto.
Qed.

Ltac simpl_pi_step :=
  (* repeat *)
  match goal with
    | [H : pi_step _ _ |- _] => induction H
    | [H : pi_step ?x ?x -> _ |- _] => clear H
  end.

Lemma pi_step_pi (Var : Set) (x y : Term Var) :
  pi_step x y -> pi x y.
Proof.
  intro H; induction H; auto.
Qed.

Instance commuting_flip_pi_pi (Var : Set) : Commuting Var (flip pi) pi.
Proof.
  apply (weaken_commuting _ _ _ (flip pi_step) pi_step); auto.
  - intros x y; rewrite weak_star_flip; compute; apply weaken_pi.
  - apply weaken_pi.
  - compute; intros x y z xy yz.
    (* TODO similar to commuting_flip_beta_beta *)
    (* OLD
    induction xy; induction yz; auto.
    *)
Admitted. 

Instance commuting_flip_pi_probe (Var : Set) :
  Commuting Var (flip pi) probe.
Proof.
  apply (weaken_commuting _ _ _ (flip pi_step) probe_step); auto.
  - intros x y; rewrite weak_star_flip; compute; apply weaken_pi.
  - apply weaken_probe.
  - compute; intros x y z xy yz.
    destruct yz.
    exists (x * TOP); repeat split; auto.
    apply (@weak_star_trans _ _ x0 x x) in xy; auto.
    rewrite <- weaken_pi in xy; auto.
Qed.

Instance commuting_pi_probe (Var : Set) : Commuting Var pi probe.
Proof.
  apply (weaken_commuting _ _ _ pi_step probe_step); auto.
  - apply weaken_pi.
  - apply weaken_probe.
  - compute; intros x y z xy yz; destruct yz; exists (x * TOP); split; auto.
    rewrite xy; reflexivity.
Qed.

(* TODO try to replace this with commuting_beta_step_pi
   since [beta TOP x -> x == TOP]? *)
Lemma beta_step_pi_top (Var : Set) (x y : Term Var) :
  beta_step x y -> (pi x TOP <-> pi y TOP).
Proof.
  intro Hb; split; intro Hp.
  - admit. (* TODO similar strategy to commuting_flip_beta_beta *)
  - rewrite Hb; auto.
Qed.

Lemma beta_pi_top (Var : Set) (x y : Term Var) :
  beta x y -> (pi x TOP <-> pi y TOP).
Proof.
  intro Hb; rewrite weaken_beta in Hb; induction Hb; try tauto.
  transitivity (pi y TOP); auto.
  apply beta_step_pi_top; auto.
Qed.

Lemma probe_pi_top (Var : Set) (x y : Term Var) :
  probe x y -> pi x TOP -> pi y TOP.
Proof.
  intro Hp; rewrite weaken_probe in Hp; induction Hp; try tauto.
  destruct H; intro H; apply IHHp.
  transitivity (TOP * TOP : Term Var); auto.
  transitivity (K * TOP * TOP : Term Var); auto.
  unfold K.
  rewrite beta_sub; compute.
  rewrite beta_sub; compute.
  auto.
Qed.


(* ------------------------------------------------------------------------ *)
(** ** Reduction and substitution *)

Lemma term_sub_proper_probe (Var Var' : Set)
  (f : Var -> Term Var') (x y : Term Var) :
  probe x y -> probe (x @ f) (y @ f).
Proof.
  intro xy; induction xy; simpl.
  - reflexivity.
  - transitivity (y @ f); auto.
  - apply probe_top; auto.
Qed.

Instance term_map_proper_beta (Var Var' : Set) :
  Proper (eq ==> beta ==> beta) (@term_map Var Var').
Proof.
  intros f f' ff' x x' xx'; rewrite <- ff'; clear f' ff'.
  revert Var' f; induction xx'; intros Var' f; simpl; auto.
  - transitivity (term_map f y); auto.
  - rewrite beta_sub.
    admit.
    (*
    dependent induction x; simpl; auto.
    *)
Qed.

Instance some_sub_proper_beta (Var Var' : Set) :
  Proper ((eq ==> beta) ==> eq ==> beta) (@some_sub Var Var').
Proof.
  intros f f' ff'; compute in ff'.
  intros v v' vv'; rewrite <- vv'; clear v' vv'.
  case_eq v; auto.
  intros v' vv'; simpl; rewrite ff'; reflexivity.
Qed.

Lemma some_sub_beta 
  (Var Var' : Set) (f g : Var -> Term Var') :
  (forall v, beta (f v) (g v)) ->
  forall v, beta (some_sub f v) (some_sub g v).
Proof.
  intros Hb v; case_eq v; auto.
  intros v' vv'; simpl; rewrite Hb; reflexivity.
Qed.

Lemma term_sub_beta_left
  (Var Var' : Set) (f g : Var -> Term Var') (x : Term Var) :
  (forall v, beta (f v) (g v)) -> beta (x @ f) (x @ g).
Proof.
  revert Var' f g; induction x; intros Var' f g fg; auto.
  - simpl; transitivity ((x1 @ g) || (x2 @ f)); auto.
  - simpl; transitivity ((x1 @ g) (+) (x2 @ f)); auto.
  - simpl; transitivity ((x1 @ g) * (x2 @ f)); auto.
  - simpl; auto.
  - simpl; apply beta_lambda.
    rewrite (IHx (option Var') (some_sub f) (some_sub g)); clear IHx;
    intros; auto.
    apply ext_respectful in fg; rewrite fg; reflexivity.
Qed.
Hint Resolve term_sub_beta_left.

Lemma lambda_app_sub_sub
  (Var : Set) (y : Term Var) (x : Term (option Var))
  (Var' : Set) (f : Var -> Term Var') :
  lambda_app_sub x y @ f = lambda_app_sub (x @ some_sub f) (y @ f).
Proof.
  revert Var' f.
  dependent induction x; intros; try (simpl; auto; reflexivity).
Admitted.

Lemma term_sub_beta_right
  (Var Var' : Set) (f : Var -> Term Var') (x y : Term Var) :
  beta x y -> beta (x @ f) (y @ f).
Proof.
  intro xy; revert Var' f; induction xy; intros Var' f;
  try (simpl; auto; reflexivity).
  - transitivity (y @ f); auto.
  - simpl; rewrite beta_sub, lambda_app_sub_sub; reflexivity.
Qed.
Hint Resolve term_sub_beta_right.

Instance term_sub_proper_beta (Var Var' : Set) :
  Proper ((eq ==> beta) ==> beta ==> beta) (@term_sub Var Var').
Proof.
  intros f g Hfg x y Hxy; transitivity (y @ f);
  [apply term_sub_beta_right | apply term_sub_beta_left]; auto.
Qed.

Lemma term_sub_pi_left
  (Var Var' : Set) (f g : Var -> Term Var') (x : Term Var) :
  (forall v, pi (f v) (g v)) -> pi (x @ f) (x @ g).
Proof.
  revert Var' f g; induction x; intros Var' f g fg; auto.
  - simpl; transitivity ((x1 @ f) || (x2 @ g)); auto.
  - simpl; transitivity ((x1 @ f) (+) (x2 @ g)); auto.
  - simpl; transitivity ((x1 @ f) * (x2 @ g)); auto.
  - simpl; auto.
  - simpl; apply pi_lambda.
    rewrite (IHx (option Var') (some_sub f) (some_sub g)); clear IHx;
    intros; auto.
    admit.
    (* TODO add Instance Proper for sub parts
    apply ext_respectful in fg; rewrite fg; reflexivity.
    *)
Qed.
Hint Resolve term_sub_pi_left.

Lemma term_sub_pi_right
  (Var Var' : Set) (f : Var -> Term Var') (x y : Term Var) :
  pi x y -> pi (x @ f) (y @ f).
Proof.
  intro xy; induction xy; repeat rewrite term_sub_ap; simpl; auto.
  - transitivity (y @ f); auto.
  - admit.
  - admit.
Qed.
Hint Resolve term_sub_pi_right.

Instance term_sub_proper_pi (Var Var' : Set) :
  Proper ((eq ==> pi) ==> pi ==> pi) (@term_sub Var Var').
Proof.
  intros f g Hfg x y Hxy; transitivity (y @ f);
  [apply term_sub_pi_right | apply term_sub_pi_left]; auto.
Qed.


(* ------------------------------------------------------------------------ *)
(** ** Reduction and closing terms *)

Instance term_close_proper_beta (Var : Set) :
  Proper (beta ==> beta) (@close Var).
Proof.
  intros x x' xx'; apply weaken_beta in xx'; induction xx'; auto.
  revert z xx' IHxx'; induction H; intros;
  try (compute; term_simpl; eauto; reflexivity).
  - unfold close; simpl.
    admit.
  - unfold close in *; simpl.
    rewrite beta_sub.
    unfold lambda_app_sub in *.
    admit.
Qed.

Instance term_close_proper_pi (Var : Set) :
  Proper (pi ==> pi) (@close Var).
Proof.
  intros x x' xx'; apply weaken_pi in xx'; induction xx'; auto.
  revert z xx' IHxx'; induction H; intros;
  try (compute; term_simpl; eauto; reflexivity).
  - admit.
  - admit.
Qed.

Lemma probe_step_close (Var : Set) (x y : Term Var) :
  probe_step x y -> probe (close x) (close y).
Proof.
  intro Hb; induction Hb; compute; auto.
Qed.

Lemma probe_close (Var : Set) (x y : Term Var) :
  probe x y -> probe (close x) (close y).
Proof.
  intro Hb; rewrite weaken_probe in Hb; induction Hb; auto.
  rewrite <- IHHb; clear Hb IHHb; auto using probe_step_close.
Qed.

Lemma beta_step_close (Var : Set) (x y : Term Var) :
  beta_step x y -> beta (close x) (close y).
Proof.
  intro Hb; induction Hb; try (compute; beta_reduce; auto).
  - admit.
  - admit.
Qed.

Lemma beta_close (Var : Set) (x y : Term Var) :
  beta x y -> beta (close x) (close y).
Proof.
  intro Hb; rewrite weaken_beta in Hb; induction Hb; auto.
  rewrite <- IHHb; clear Hb IHHb; auto using beta_step_close.
Qed.

Lemma pi_step_close (Var : Set) (x y : Term Var) :
  pi_step x y -> pi (close x) (close y).
Proof.
  intro Hb; induction Hb; try (compute; beta_reduce; auto).
  - admit.
  - admit.
Qed.

Lemma pi_close (Var : Set) (x y : Term Var) :
  pi x y -> pi (close x) (close y).
Proof.
  intro Hb; rewrite weaken_pi in Hb; induction Hb; auto.
  rewrite <- IHHb; clear Hb IHHb; auto using pi_step_close.
Qed.
