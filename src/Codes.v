
Require Import Setoid.
Require Import Notations.

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
  | beta_j x y z : beta ((x || y) * z) (x * z || y * z)
  | beta_i x : beta (I * x) x
  | beta_k x y : beta (K * x * y) x
  | beta_b x y z : beta (B * x * y * z) (x * (y * z))
  | beta_c x y z : beta (C * x * y * z) (x * z * y)
  | beta_s x y z : beta (S * x * y * z) (x * z * (y * z))
  | beta_y x : beta (Y * x) (x * (Y * x))
  | beta_v x : beta (V * x) (I || x o (V * x)).

Inductive pi {Var : Set} : Code Var -> Code Var -> Prop :=
  | pi_top x : pi TOP x
  | pi_bot x : pi x BOT
  | pi_j_left x y : pi (x || y) x
  | pi_j_right x y : pi (x || y) y.

Inductive red {Var : Set} : Code Var -> Code Var -> Prop :=
  | red_refl x : red x x
  | red_trans x y z : red x y -> red y z -> red x z
  | red_ap_left x x' y : red x x' -> red (x * y) (x' * y)
  | red_ap_right x y y' : red y y' -> red (x * y) (x * y')
  | red_beta x y : beta x y -> red x y
  | red_beta' x y : beta y x -> red x y
  | red_pi x y : pi x y -> red x y.

Hint Constructors beta.
Hint Constructors pi.
Hint Constructors red.

Fixpoint try_red_step {Var : Set} (u : Code Var) : option (Code Var) :=
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
      match try_red_step x with
      | Some x' => Some (x' * y)
      | None =>
          match try_red_step y with
          | Some y' => Some (x * y')
          | None => None
          end
      end
  | _ => None
  end.

Section try_red_step.
  Variable Var : Set.
  Variable x : Code Var.
  Eval compute in
    (try_red_step ((x || (C * I * TOP) o (V * (C * I * TOP)) * x))).
End try_red_step.

Ltac red_to x := apply red_trans with x; auto.

Ltac red_step_ try_red_step :=
  match goal with
  | [|- @red ?v ?x ?y] =>
      match eval compute in (try_red_step v x) with
      | Some ?z => red_to z
      | _ => fail
      end
  | _ => fail
  end.

Ltac red_step := red_step_ @try_red_step.

Definition code_div {Var : Set} : Code Var := V * (C * I * TOP).
Lemma red_div {Var : Set} (x : Code Var) :
  red (code_div * x) (x || code_div * x * TOP).
Proof.
  unfold code_div.
  red_step.
  red_step.
  red_step.
  apply red_ap_right. (* FIXME allow variables in red_step *)
  red_step.
  red_step.
Qed.

Definition conv {Var : Set} (x : Code Var) := red (code_div * x) TOP.

Ltac conv_to x := unfold conv; red_to x; fold conv.

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

Notation "x @ f" := (code_sub f x)%code : code_scope.

Lemma var_monad_unit_right (Var : Set) (x : Code Var) : x @ code_var = x.
Proof.
  induction x; auto.
  unfold code_sub; fold (@code_sub Var Var).
  rewrite IHx1; rewrite IHx2; auto.
Qed.
Hint Rewrite var_monad_unit_right.

Lemma var_monad_unit_left (Var Var' : Set) (f : Var -> Code Var') x :
  (code_var x) @ f = f x.
Proof.
  compute; auto.
Qed.
Hint Rewrite var_monad_unit_left.

Lemma code_sub_ap (Var Var' : Set)
  (x y : Code Var) (f : Var -> Code Var') : (x * y @ f) = (x @ f) * (y @ f).
Proof.
  simpl; auto.
Qed.
Hint Rewrite code_sub_ap.

Lemma var_monad_assoc
  (Var Var' Var'' : Set)
  (f : Var -> Code Var')
  (g : Var' -> Code Var'')
  (x : Code Var) :
  (x @ f) @ g = x @ (fun v => (f v) @ g).
Proof.
  induction x; auto.
  repeat rewrite code_sub_ap.
  rewrite IHx1; rewrite IHx2; auto.
Qed.
Hint Rewrite var_monad_assoc.

Lemma code_sub_ext {Var Var' : Set}
  (f g : Var -> Code Var') (fg : forall v, f v = g v) x :
  x @ f = x @ g.
Proof.
  induction x; simpl; auto.
  rewrite IHx1; rewrite IHx2; auto.
Qed.

Lemma red_sub_left {Var Var' : Set}
  (f g : Var -> Code Var') (fg : forall v, red (f v) (g v))
  (x : Code Var) : red (x @ f) (x @ g).
Proof.
  induction x; auto.
    compute; auto.
  unfold code_sub; fold (@code_sub Var Var').
  red_to ((x1 @ f) * (x2 @ g)).
Qed.
Hint Resolve red_sub_left.

Lemma beta_sub_right {Var Var' : Set}
  (f : Var -> Code Var') (x y : Code Var)
  (xy : beta x y) : beta (x @ f) (y @ f).
Proof.
  induction xy; repeat rewrite code_sub_ap; simpl; auto.
Qed.
Hint Resolve beta_sub_right.

Lemma pi_sub_right {Var Var' : Set}
  (f : Var -> Code Var') (x y : Code Var)
  (xy : pi x y) : pi (x @ f) (y @ f).
Proof.
  induction xy; repeat rewrite code_sub_ap; simpl; auto.
Qed.
Hint Resolve pi_sub_right.

Lemma red_sub_right {Var Var' : Set}
  (f : Var -> Code Var') (x y : Code Var)
  (xy : red x y) : red (x @ f) (y @ f).
Proof.
  induction xy; repeat rewrite code_sub_ap; simpl; auto.
  apply red_trans with (y @ f); auto.
Qed.
Hint Resolve red_sub_right.

Lemma red_sub {Var Var' : Set}
  {f g : Var -> Code Var'} (fg : forall v, red (f v) (g v))
  {x y : Code Var} (xy : red x y) :
  red (code_sub f x) (code_sub g y).
Proof.
  red_to (code_sub g x).
Qed.
Hint Resolve red_sub.

(** Contexts, convergence, and information ordering *)

Definition code_le {Var : Set} (x y : Code Var) :=
  forall {Var' : Set} (c : Code Var') (f : Var -> Code Var'),
  conv (c * (x @ f)) -> conv (c * (y @ f)).

Notation "x [= y" := (code_le x y)%code : code_scope.

Lemma code_le_refl {Var : Set} (x : Code Var) : x [= x.
Proof.
  unfold code_le; auto.
Qed.
Hint Resolve code_le_refl.

Lemma code_le_trans {Var : Set} (x y z : Code Var) :
  x [= y -> y [= z -> x [= z .
Proof.
  unfold code_le; auto.
Qed.
Hint Resolve code_le_trans.

Lemma code_le_ap_right {Var : Set} {x y y' : Code Var} :
  y [= y' -> x * y [= x * y'.
Proof.
  unfold code_le; unfold conv; intros H Var' c f.
  repeat rewrite code_sub_ap.
  intros Hconv.
  red_to (code_div * ((c o (x @ f)) * (y' @ f))).
  apply H.
  red_to (code_div * (c * ((x @ f) * (y @ f)))).
Qed.
Hint Resolve code_le_ap_right.

Lemma code_le_ap_left {Var : Set} {x x' y : Code Var} :
  x [= x' -> x * y [= x' * y.
Proof.
  unfold code_le; unfold conv; intros H Var' c f.
  repeat rewrite code_sub_ap.
  intros Hconv.
  red_to (code_div * (c * (I * (x' @ f) * (y @ f)))).
  red_to (code_div * (c * (C * I * (y @ f) * (x' @ f)))).
  red_to (code_div * (c o (C * I * (y @ f)) * (x' @ f))).
  apply H.
  red_to (code_div * (c * (C * I * (y @ f) * (x @ f)))).
  red_to (code_div * (c * (I * (x @ f) * (y @ f)))).
  red_to (code_div * (c * ((x @ f) * (y @ f)))).
Qed.
Hint Resolve code_le_ap_left.

Lemma code_le_ap {Var : Set} {x x' y y': Code Var} :
  code_le x x' -> code_le y y' -> code_le (x * y) (x' * y').
Proof.
  intros Hx Hy.
  apply code_le_trans with (x * y'); auto.
Qed.
Hint Resolve code_le_ap.

Lemma code_le_red_left {Var : Set} (x x' y : Code Var) :
  red x x' -> x [= y -> x' [= y.
Proof.
  unfold code_le; intros Hred Hxy Var' c f Hconv.
  apply Hxy.
  red_to (code_div o c * (x @ f)).
  red_to (code_div o c * (x' @ f)).
  red_to (code_div * (c * (x' @ f))).
Qed.
Hint Resolve code_le_red_left.

Lemma code_le_red_right {Var : Set} (x y y' : Code Var) :
  red y' y -> x [= y -> x [= y'.
Proof.
  unfold code_le; intros Hred Hxy Var' c f Hconv.
  red_to (code_div o c * (y' @ f)).
  red_to (code_div o c * (y @ f)).
  red_to (code_div * (c * (y @ f))).
  apply Hxy; auto.
Qed.
Hint Resolve code_le_red_right.

Lemma code_le_red {Var : Set} (x x' y y' : Code Var) :
  red x x' -> red y' y -> x [= y -> x' [= y'.
Proof.
  intros Hx Hy Hxy.
    apply code_le_red_right with y; auto.
  apply code_le_red_left with x; auto.
Qed.
Hint Resolve code_le_red.

Lemma code_le_top {Var : Set} (x : Code Var) : x [= TOP.
Proof.
  unfold code_le; intros Var' c f Hred.
  red_to (code_div o c * TOP).
  red_to (code_div o c * (x @ f)).
  red_to (code_div * (c * (x @ f))).
Qed.
Hint Resolve code_le_top.

Lemma code_le_bot {Var : Set} (x : Code Var) : BOT [= x.
Proof.
  unfold code_le; intros Var' c f Hred.
  red_to (code_div o c * (x @ f)).
  red_to (code_div o c * BOT).
  red_to (code_div * (c * BOT)).
Qed.
Hint Resolve code_le_bot.

Lemma code_le_j_left {Var : Set} (x y : Code Var) : x [= x || y.
Proof.
  unfold code_le; intros Var' c f Hred.
  red_to (code_div * (c * (x @ f))).
Qed.
Hint Resolve code_le_j_left.

Lemma code_le_j_right {Var : Set} (x y : Code Var) : y [= x || y.
Proof.
  unfold code_le; intros Var' c f Hred.
  red_to (code_div * (c * (y @ f))).
Qed.
Hint Resolve code_le_j_right.

Lemma code_le_j_ub {Var : Set} (x y z : Code Var) :
  x [= z -> y [= z -> x || y [= z.
Proof.
  unfold code_le; unfold conv; intros Hx Hy Var' c f Hconv.
  (* TODO *)
Admitted.
Hint Resolve code_le_j_ub.

Lemma code_le_ext {Var : Set} (x x' : Code Var) :
  (forall y, x * y [= x' * y) -> x [= x'.
Proof.
  (* TODO implement via abstraction algorithm *)
Admitted.
Hint Resolve code_le_ext.

(** ** Observational equivalence *)

Definition code_eq {Var : Set} (x y : Code Var) := x [= y /\ y [= x.
Notation "x [=] y" := (code_eq x y)%code : code_scope.

Lemma code_eq_beta {Var : Set} (x y : Code Var) : beta x y -> x [=] y.
Proof.
  unfold code_eq; intros Hbeta; split.
  assert (Hxy : red x y); auto; apply code_le_red_left with y; auto.
  assert (Hyx : red y x); auto; apply code_le_red_right with y; auto.
Qed.
Hint Resolve code_eq_beta.

Lemma code_eq_ext {Var : Set} (x x' : Code Var) :
  (forall y, x * y [=] x' * y) -> x [=] x'.
Proof.
  unfold code_eq; intro H; split; apply code_le_ext; intro y; apply H.
Qed.
Hint Resolve code_eq_ext.
