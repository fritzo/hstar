(** * Type assignment and type checking *)

Require Import Coq.Program.Basics.
Require Import Coq.Program.Equality.
Require Import Coq.Setoids.Setoid.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Logic.Decidable.
Require Import Coq.Bool.Bool.
Require Export BohmTrees.

Open Scope code_scope.
Open Scope term_scope.

(* ------------------------------------------------------------------------ *)
(** ** Types *)

Inductive Tp {Vs : Set} : Set :=
  | Tp_var : Vs -> Tp
  | Tp_exp : Tp -> Tp -> Tp
  | Tp_bind : @Tp (option Vs) -> Tp.
  (* TODO allow constants like [I] and [bool] *)
  (* TODO allow recursion via mu *)
Hint Constructors Tp.
Arguments Tp : default implicits.

Notation "'VAR'" := Tp_var : tp_scope.
Notation "'BIND'" := Tp_bind : tp_scope.

Open Scope tp_scope.
Delimit Scope tp_scope with tp.
Bind Scope tp_scope with Tp.

Notation "x --> y" := (Tp_exp x y)%tp : tp_scope.

Section tp_sub.
  Fixpoint tp_map {Vs Vs' : Set} (f : Vs -> Vs') (x : Tp Vs) : Tp Vs' :=
    match x with
    | Tp_var v => Tp_var (f v)
    | Tp_exp x1 x2 => Tp_exp (tp_map f x1) (tp_map f x2)
    | Tp_bind x1 => Tp_bind (tp_map (option_map f) x1)
    end.

  Definition tp_some_sub {Vs Vs' : Set} (f : Vs -> Tp Vs') (v : option Vs) :
    Tp (option Vs') :=
    match v with
    | None => Tp_var None
    | Some v' => tp_map (@Some Vs') (f v')
    end.

  Fixpoint tp_sub {Vs Vs' : Set} (f : Vs -> Tp Vs') (x : Tp Vs) : Tp Vs' :=
    match x with
    | Tp_var v => f v
    | Tp_exp x1 x2 => Tp_exp (tp_sub f x1) (tp_sub f x2)
    | Tp_bind x1 => Tp_bind (tp_sub (tp_some_sub f) x1)
    end.
End tp_sub.

Definition A {Vs : Set} : Term Vs. Admitted.

Section eval_type.
  Definition flip_var {Ts Vs : Set} (v : Ts + Ts + Vs) : Ts + Ts + Vs :=
    match v with
    | inl (inl v') => inl (inr v')
    | inl (inr v') => inl (inl v')
    | inr v' => inr v'
    end.

  Definition term_exp {Vs : Set} (a b : Term Vs) : Term Vs :=
    let Vs' : Set := option (option Vs) in
    let f : Term Vs' := term_var None in
    let x : Term Vs' := term_var (Some None) in
    let a' : Term Vs' := term_map (fun v => Some (Some v)) a in
    let b' : Term Vs' := term_map (fun v => Some (Some v)) b in
    term_lambda (term_lambda (b' * (f * (a' * x)))).

  Definition eval_var {Ts Vs : Set} (v : option Ts + option Ts + Vs) :
    option (option (Ts + Ts + Vs)) :=
    match v with
    | inl (inl None) => None
    | inl (inr None) => Some None
    | inl (inl (Some v')) => Some (Some (inl (inl v')))
    | inl (inr (Some v')) => Some (Some (inl (inr v')))
    | inr v' => Some (Some (inr v'))
    end.

  Definition bind_var {Vs : Set} (x : Term (option (option Vs))) : Term Vs :=
    A * LAMBDA (LAMBDA x).

  Fixpoint eval_type' {Ts Vs : Set} (a : Tp Ts) : Term (Ts + Ts + Vs) :=
    match a with
    | Tp_var v => term_var (inl (inl v))
    | Tp_exp a b =>
        let a' := eval_type' a in
        let b' := eval_type' b in
        term_exp (term_map flip_var a') b'
    | Tp_bind a =>
        let a' := eval_type' a in
        bind_var (term_map eval_var a')
    end.

  Definition close_type {Vs : Set} :
    Term (Empty_set + Empty_set + Vs) -> Term Vs :=
    term_map (fun v =>
    match v with
    | inr v' => v'
    | inl (inr v') => match v' : Empty_set with end
    | inl (inl v') => match v' : Empty_set with end
    end).

  Definition eval_type {Vs : Set} (a : Tp Empty_set) : Term Vs :=
    close_type (eval_type' a).
End eval_type.

(* ------------------------------------------------------------------------ *)
(** ** Type-annotated normal forms *)

Inductive Normal {Ts Vs : Set} : Set :=
  | Normal_top : Normal
  | Normal_bot : Normal
  | Normal_join : Normal -> Normal -> Normal
  | Normal_rand : Normal -> Normal -> Normal
  | Normal_inert : Inert -> Normal
  | Normal_lambda : @Normal Ts (option Vs) -> Normal
  | Normal_ann : Tp Ts -> Normal -> Normal
with Inert {Ts Vs : Set} : Set :=
  | Inert_var : Vs -> Inert
  | Inert_app : Inert -> Normal -> Inert
  | Inert_ann : Tp Ts -> Inert -> Inert.
Hint Constructors Normal Inert.
Arguments Normal : default implicits.
Arguments Inert : default implicits.

Notation "'TOP'" := Normal_top : normal_scope.
Notation "'BOT'" := Normal_bot : normal_scope.
Notation "'LAMBDA'" := Normal_lambda : normal_scope.
Notation "'VAR'" := Inert_var : inert_scope.

Open Scope inert_scope.
Open Scope normal_scope.
Delimit Scope normal_scope with normal.
Delimit Scope inert_scope with inert.
Bind Scope normal_scope with Normal.
Bind Scope inert_scope with Inert.

Notation "[ x ]" := (Normal_inert x)%normal : normal_scope.
Notation "x * y" := (Inert_app x y)%inert : inert_scope.
Notation "x || y" := (Normal_join x y)%normal : normal_scope.
Notation "x (+) y" := (Normal_rand x y)%normal : normal_scope.
Reserved Notation "x $ y" (at level 56, right associativity).
Notation "a $ x" := (Normal_ann a x)%normal : normal_scope.
Notation "a $ x" := (Inert_ann a x)%inert : inert_scope.

(*
Fixpoint is_untyped_normal {Ts Vs : Set} (x : Normal Ts Vs) : bool :=
  match x with
  | TOP => TOP
  | BOT => BOT
  | x1 || x2 => is_untyped_normal x1 || is_untyped_normal x2
  | x1 (+) x2 => is_untyped_normal x1 (+) is_untyped_normal x2
  | [i] => [is_untyped_inert i]
  | Normal_lambda x1 => LAMBDA (normal_map (option_map f) x1)
  | a $ x1 => a $ is_untyped_normal x1
  end
with is_untyped_inert {Ts Vs : Set}  (x : Inert Ts Vs) : bool :=
  match x with
  | x1 * x2 => is_untyped_inert x1 * is_untyped_normal x2
  | Inert_var v => Inert_var (f v)
  | (a1 $ x1)%inert => (a1 $ is_untyped_inert x1)%inert
  end.
*)

Section normal_sub.
  Fixpoint normal_map {Vs Vs' Ts : Set} (f : Vs -> Vs') (x : Normal Ts Vs) :
    Normal Ts Vs' :=
    match x with
    | TOP => TOP
    | BOT => BOT
    | x1 || x2 => normal_map f x1 || normal_map f x2
    | x1 (+) x2 => normal_map f x1 (+) normal_map f x2
    | [i] => [inert_map f i]
    | Normal_lambda x1 => LAMBDA (normal_map (option_map f) x1)
    | a $ x1 => a $ normal_map f x1
    end
  with inert_map {Ts Vs Vs' : Set}  (f : Vs -> Vs') (x : Inert Ts Vs) :
    Inert Ts Vs' :=
    match x with
    | x1 * x2 => inert_map f x1 * normal_map f x2
    | Inert_var v => VAR (f v)
    | (a1 $ x1)%inert => (a1 $ inert_map f x1)%inert
    end.

  Definition normal_some_sub
    {Ts Vs Vs' : Set} (f : Vs -> Inert Ts Vs') (v : option Vs) :
    Inert Ts (option Vs') :=
    match v with
    | None => VAR None
    | Some v' => inert_map (@Some Vs') (f v')
    end.

  Fixpoint normal_sub
    {Ts Vs Vs' : Set} (f : Vs -> Inert Ts Vs') (x : Normal Ts Vs) :
    Normal Ts Vs' :=
    match x with
    | TOP => TOP
    | BOT => BOT
    | x1 || x2 => normal_sub f x1 || normal_sub f x2
    | x1 (+) x2 => normal_sub f x1 (+) normal_sub f x2
    | [i] => [inert_sub f i]
    | Normal_lambda x1 => LAMBDA (normal_sub (normal_some_sub f) x1)
    | a $ x1 => a $ normal_sub f x1
    end
  with
    inert_sub
    {Ts Vs Vs' : Set}  (f : Vs -> Inert Ts Vs') (x : Inert Ts Vs) :
    Inert Ts Vs' :=
    match x with
    | x1 * x2 => inert_sub f x1 * normal_sub f x2
    | Inert_var v => f v
    | (a1 $ x1)%inert => (a1 $ inert_sub f x1)%inert
    end.

  Fixpoint normal_tp_sub
    {Ts Ts' Vs : Set} (f : Ts -> Tp Ts') (x : Normal Ts Vs) :
    Normal Ts' Vs :=
    match x with
    | TOP => TOP
    | BOT => BOT
    | x1 || x2 => normal_tp_sub f x1 || normal_tp_sub f x2
    | x1 (+) x2 => normal_tp_sub f x1 (+) normal_tp_sub f x2
    | [i] => [inert_tp_sub f i]
    | Normal_lambda x1 => LAMBDA (normal_tp_sub f x1)
    | a $ x1 => tp_sub f a $ normal_tp_sub f x1
    end
  with
    inert_tp_sub
    {Ts Ts' Vs : Set}  (f : Ts -> Tp Ts') (x : Inert Ts Vs) :
    Inert Ts' Vs :=
    match x with
    | x1 * x2 => inert_tp_sub f x1 * normal_tp_sub f x2
    | Inert_var v => VAR v
    | (a $ x1)%inert => (tp_sub f a $ inert_tp_sub f x1)%inert
    end.
End normal_sub.

Fixpoint eval_normal {Vs : Set} (x : Normal Empty_set Vs) : Term Vs :=
  match x with
  | TOP => term_top
  | BOT => term_bot
  | x1 || x2 => (eval_normal x1 || eval_normal x2)%term
  | x1 (+) x2 => (eval_normal x1 (+) eval_normal x2)%term
  | [i] => eval_inert i
  | Normal_lambda x1 => term_lambda (eval_normal x1)
  | a $ x1 => (eval_type a * eval_normal x1)%term
  end
with eval_inert {Vs : Set} (x : Inert Empty_set Vs) : Term Vs :=
  match x with
  | x1 * x2 => (eval_inert x1 * eval_normal x2)%term
  | Inert_var v => term_var v
  | (a1 $ x1)%inert => (eval_type a1 * eval_inert x1)%term
  end.

Fixpoint quote_normal {Vs : Set} (x : Term Vs) : Normal Empty_set Vs :=
  match x with
  | term_top => TOP
  | term_bot => BOT
  | term_join x1 x2 => quote_normal x1 || quote_normal x2
  | term_rand x1 x2 => quote_normal x1 (+) quote_normal x2
  | term_lambda x1 => LAMBDA (quote_normal x1)
  | term_var v => [VAR v]
  | term_app x1 x2 =>
      match quote_normal x1 with
      | [x1'] => [x1' * quote_normal x2]
      | _ => BOT
      end
  end.

Lemma eval_quote_normal_le (Vs : Set) (x : Term Vs) :
  eval_normal (quote_normal x) [= x.
Proof.
  induction x; simpl; try (term_to_code; reflexivity).
  - case_eq (quote_normal x1); intros; simpl; try (term_to_code ; reflexivity).
    rewrite <- IHx1, IHx2, H; simpl; reflexivity.
  - rewrite IHx; reflexivity.
Qed.

Lemma quote_normal_not_ann (Vs : Set) (x : Term Vs) a y :
  ~ quote_normal x = a $ y.
Proof.
  destruct x; intro H; try (inversion H; reflexivity).
  simpl in H; case_eq (quote_normal x1);
  intros until 0; intro eq; rewrite eq in H; inversion H.
Qed.

Lemma eval_quote_normal (Vs : Set) (x : Term Vs) :
  normal x -> eval_normal (quote_normal x) = x.
Proof.
  induction x; intro Hn; simpl; auto.
  - inversion_clear Hn; [rewrite IHx1, IHx2; auto | inversion_clear H].
  - inversion_clear Hn; [rewrite IHx1, IHx2; auto | inversion_clear H].
  - case_eq (quote_normal x1); intros; simpl; auto;
    inversion_clear Hn; inversion_clear H0;
    rewrite H in IHx1; simpl in IHx1; assert (normal x1) by auto;
    try (rewrite <- IHx1 in H1 by auto; inversion H1; reflexivity).
    + rewrite IHx1, IHx2 by auto; auto.
    + apply quote_normal_not_ann in H; contradiction.
  - inversion Hn; rewrite IHx; auto.
    inversion H.
Qed.

(* ------------------------------------------------------------------------ *)
(** ** Type checking *)

Definition ann_sub {Ts Vs : Set} (a : Tp Ts) :
  Normal Ts (option Vs) -> Normal Ts (option Vs) :=
  normal_sub (
    fun v =>
    match v with
    | None => (a $ (VAR None))%inert
    | Some v => VAR (Some v)
    end).

(* TODO How to use [exp_sub] in a homogeneous relation? *)
(* TODO How to use [exp_sub] on a var other than the latest-bound? *)
Definition exp_sub {Ts : Set} : Tp (option Ts) -> Tp (option (option Ts)) :=
  tp_sub (
    fun v =>
    match v with
    | None => VAR None --> VAR (Some None)
    | Some v' => (VAR (Some (Some v')))%tp
    end).

Inductive refines {Ts : Set} : relation (Tp Ts) :=
  | refines_refl a : refines a a
  | refines_trans a b c : refines a b -> refines b c -> refines a c
  | refines_exp_left a a' b : refines a a' -> refines (a --> b) (a' --> b)
  | refines_exp_right a b b' : refines b b' -> refines (a --> b) (a --> b')
  | refines_bind a b : @refines (option Ts) a b -> refines (BIND a) (BIND b)
  | refines_conjugate a : refines (BIND a) (BIND (BIND (exp_sub a))).

(* TODO deal with type binders, maybe with checks_unbind *)
(* TODO keep track of type variance *)
Inductive checks {Ts Vs : Set} : relation (Normal Ts Vs) :=
  (* kleene algebra *)
  | checks_refl x : checks x x
  | checks_trans x y z : checks x y -> checks y z -> checks x z
  (* respectful *)
  | checks_join_left x x' y : checks x x' -> checks (x || y) (x' || y)
  | checks_join_right x y y' : checks y y' -> checks (x || y) (x || y')
  | checks_rand_left x x' y : checks x x' -> checks (x (+) y) (x' (+) y)
  | checks_rand_right x y y' : checks y y' -> checks (x (+) y) (x (+) y')
  | checks_inert x y : checks' x y -> checks [x] [y]
  | checks_lambda x y :
      @checks Ts (option Vs) x y -> checks (LAMBDA x) (LAMBDA y)
  (* expansion *)
  | checks_eta_expand x : checks x (LAMBDA (normal_map (@Some Vs) x))
  | checks_expand_top a : checks (a $ TOP) TOP
  | checks_expand_bot a : checks (a $ BOT) BOT
  | checks_expand_join a x y : checks (a $ x || y) ((a $ x) || (a $ y))
  | checks_expand_rand a x y : checks (a $ x (+) y) ((a $ x) (+) (a $ y))
  | checks_expand_lambda a b x :
      checks (a --> b $ LAMBDA x) (LAMBDA (b $ ann_sub a x))
  | checks_expand_inert a x : checks (a $ [x]) [(a $ x)%inert]
  | checks_expand_normal a x : checks [(a $ x)%inert] (a $ [x])
  (* unification *)
  | checks_refines a a' x : refines a a' -> checks (a $ x) (a' $ x)
  | checks_identity a x : checks (a $ a $ x) x  (* TODO track variance *)
  | checks_clash a b x : a <> b -> checks (a $ b $ x) TOP
  | checks_bubble_app a x : checks [(a $ x * TOP)%inert] TOP
  | checks_bubble_lambda : checks (LAMBDA TOP) TOP
  | checks_bubble_left x : checks (TOP || x) TOP
  | checks_bubble_right x : checks (x || TOP) TOP
with checks' {Ts Vs : Set} : relation (Inert Ts Vs) :=
  (* kleene algebra *)
  | checks_refl' x : checks' x x
  | checks_trans' x y z : checks' x y -> checks' y z -> checks' x z
  (* respectful *)
  | checks_app_left x x' y : checks' x x' -> checks' (x * y) (x' * y)
  | checks_app_right x y y' : checks y y' -> checks' (x * y) (x * y')
  (* expansion *)
  | checks_expand_app a b f x :
      checks' (a --> b $ f * x)%inert (b $ f * (a $ x)%normal)%inert.

Instance eval_proper_le (Vs : Set) :
  Proper (checks --> term_le) (@eval_normal Vs).
Proof.
  intros y x xy; induction xy; simpl;
  admit.
  (* SLOW
  try (term_to_code; auto; reflexivity).
  - transitivity (eval_normal y); auto.
  - admit. (* TODO define [eval_type] *)
  - admit.
    (* TODO show [eval_type a (x (+) y) [= eval_type a x (+) eval_type a y]. *)
  - admit.
  - admit.
  *)
Qed.

(*
Lemma quote_proper_le (Vs : Set) (x y : Term Vs) :
  normal x -> normal y -> x
  Proper (term_le --> prod --> checks) (@quote_normal Vs).
*)

(** These definition of [fixes] and [raises] are a bit too tricky,
    relying on a lemma that [quote_normal _] is unannotated.
    *)

Inductive fixes {Vs : Set} (a : Tp Empty_set) : Term Vs -> Prop :=
  fixes_intro x :
    normal x ->
    checks (a $ quote_normal x) (quote_normal x) ->
    fixes a x.
Hint Constructors fixes.

Inductive raises {Vs : Set} (a : Tp Empty_set) : relation (Term Vs) :=
  raises_intro x y :
    normal x -> normal y ->
    checks (a $ quote_normal x) (quote_normal y) ->
    checks (a $ quote_normal y) (quote_normal y) ->
    raises a x y.
Hint Constructors raises.

Lemma fixes_raises (Vs : Set) (a : Tp Empty_set) (x : Term Vs) :
  fixes a x <-> raises a x x.
Proof.
  split; intro H; inversion H; auto.
Qed.

Theorem raises_sound (Vs : Set) (a : Tp Empty_set) (x y : Term Vs) :
  raises a x y -> (eval_type a * x)%term == y.
Proof.
  intro H; destruct H as [x y Hnx Hny Haxy Hayy].
  remember (quote_normal x) as x'.
  remember (quote_normal y) as y'.
  assert (eval_normal x' = x) as Ex;
    [rewrite Heqx'; apply eval_quote_normal; auto|].
  assert (eval_normal y' = y) as Ey;
    [rewrite Heqy'; apply eval_quote_normal; auto|].
  split.
  - admit. (* TODO ??? *)
  - apply eval_proper_le in Haxy; term_to_code in Haxy.
    rewrite Ex, Ey in Haxy; rewrite Haxy; simpl; reflexivity.
Qed.

Theorem raises_complete (Vs : Set) (a : Tp Empty_set) (x y : Term Vs) :
  normal x -> normal y -> (eval_type a * x)%term == y -> raises a x y.
Proof.
  intros Hnx Hny Heq.
  admit.
Qed.

Lemma fixes_sound (Vs : Set) (a : Tp Empty_set) (x : Term Vs) :
  fixes a x -> x :: eval_type a.
Proof.
  rewrite fixes_raises; apply raises_sound.
Qed.

Lemma fixes_complete (Vs : Set) (a : Tp Empty_set) (x : Term Vs) :
  normal x -> x :: eval_type a -> fixes a x.
Proof.
  rewrite fixes_raises; intros; apply raises_complete; auto.
Qed.

(* ------------------------------------------------------------------------ *)
(** ** Deterministic type checking *)

Fixpoint check_step {Ts Vs : Set} (x : Normal Ts Vs) :
  option (Normal Ts Vs) :=
  match x with
  (* TODO *)
  | _ => None
  end
with check_step' {Ts Vs : Set} (x : Inert Ts Vs) :
  option (Inert Ts Vs) :=
  match x with
  (* TODO *)
  | _ => None
  end.

Fixpoint check_step_checks (Ts Vs : Set) (x : Normal Ts Vs) :
  match check_step x with
  | None => True
  | Some y => checks x y
  end
with check_step_checks' (Ts Vs : Set) (x : Inert Ts Vs) :
  match check_step' x with
  | None => True
  | Some y => checks' x y
  end.
Proof.
  - admit.
  - admit.
Admitted.

Fixpoint try_check {Ts Vs : Set} (n : nat) (x : Normal Ts Vs) : option bool :=
  match n with
  | 0%nat => None
  | Datatypes.S n' =>
    match check_step x with
    | Some x' => try_check n' x'
    | None => (* TODO *) Some false
    end
  end.
