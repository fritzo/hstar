Require Import Setoid.
Require Import EqNat.
Require Export Notations.

Definition Succ := S%nat. (* an alias for later *)

(** * Combinatory algebra with parametric variables *)

Inductive code {Var : Set} : Set :=
  | code_var : Var -> code
  | code_ap : code -> code -> code
  | code_top : code
  | code_bot : code
  | code_j : code
  | code_r : code
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

Open Scope code_scope.
Delimit Scope code_scope with code.
Bind Scope code_scope with code.

Notation "'TOP'" := code_top : code_scope.
Notation "'BOT'" := code_bot : code_scope.
Notation "'J'" := code_j : code_scope.
Notation "'R'" := code_r : code_scope.
Notation "'I'" := code_i : code_scope.
Notation "'K'" := code_k : code_scope.
Notation "'B'" := code_b : code_scope.
Notation "'C'" := code_c : code_scope.
Notation "'S'" := code_s : code_scope.
Notation "'Y'" := code_y : code_scope.
Notation "'V'" := code_v : code_scope.
Notation "x 'o' y" := (code_b * x * y)%code : code_scope.
Notation "x || y" := (code_j * x * y)%code : code_scope.
Notation "x (+) y" := (code_r * x * y)%code : code_scope.

Definition code_join {Var : Set} x y : Code Var := x || y.

Inductive beta {Var : Set} : Code Var -> Code Var -> Prop :=
  | beta_i x : beta (I * x) x
  | beta_k x y : beta (K * x * y) x
  | beta_b x y z : beta (B * x * y * z) (x * (y * z))
  | beta_c x y z : beta (C * x * y * z) (x * z * y)
  | beta_s x y z : beta (S * x * y * z) (x * z * (y * z))
  | beta_y x : beta (Y * x) (x * (Y * x))
  | beta_v x : beta (V * x) (I || x o (V * x))
  | beta_j_ap x y z : beta ((x || y) * z) (x * z || y * z)
  | beta_r_ap x y z : beta ((x (+) y) * z) (x * z (+) y * z)
  | beta_r_idem x : beta (x (+) x) x
  | beta_r_sym x y : beta (x (+) y) (y (+) x)
  | beta_r_sym_sym w x y z : beta ((w(+)x) (+) (y(+)z))
                                  ((x(+)y) (+) (z(+)w)).

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

Inductive prob {Var : Set} : Code Var -> Prop :=
  | prob_top : prob TOP
  | prob_bot : prob BOT
  | prob_r p q : prob p -> prob q -> prob (p (+) q).

Hint Constructors beta.
Hint Constructors pi.
Hint Constructors red.
Hint Constructors prob.

Fixpoint try_red_step {Var : Set} (u : Code Var) : option (Code Var) :=
  match u with
  | I * x => Some x
  | K * x * y => Some x
  | J * x * y * z => Some (x * z || y * z)
  | R * x * y * z => Some (x * z (+) y * z)
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
Lemma red_div (Var : Set) (x : Code Var) :
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

Definition pconv {Var : Set} (x : Code Var) (pp : {p : Code Var | prob p}) :=
    let (p, _) := pp in red (code_div * x) p.

(** ** Substitution *)

Fixpoint code_sub {Var Var' : Set}
  (f : Var -> Code Var') (x : Code Var) : Code Var' :=
  match x with
  | code_var v => f v
  | l * r => (code_sub f l) * (code_sub f r)
  | TOP => TOP
  | BOT => BOT
  | J => J
  | R => R
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

Lemma code_sub_ext (Var Var' : Set)
  (f g : Var -> Code Var') (fg : forall v, f v = g v) x :
  x @ f = x @ g.
Proof.
  induction x; simpl; auto.
  rewrite IHx1; rewrite IHx2; auto.
Qed.

Lemma red_sub_left (Var Var' : Set)
  (f g : Var -> Code Var') (fg : forall v, red (f v) (g v))
  (x : Code Var) : red (x @ f) (x @ g).
Proof.
  induction x; auto.
    compute; auto.
  unfold code_sub; fold (@code_sub Var Var').
  red_to ((x1 @ f) * (x2 @ g)).
Qed.
Hint Resolve red_sub_left.

Lemma beta_sub_right (Var Var' : Set)
  (f : Var -> Code Var') (x y : Code Var)
  (xy : beta x y) : beta (x @ f) (y @ f).
Proof.
  induction xy; repeat rewrite code_sub_ap; simpl; auto.
Qed.
Hint Resolve beta_sub_right.

Lemma pi_sub_right (Var Var' : Set)
  (f : Var -> Code Var') (x y : Code Var)
  (xy : pi x y) : pi (x @ f) (y @ f).
Proof.
  induction xy; repeat rewrite code_sub_ap; simpl; auto.
Qed.
Hint Resolve pi_sub_right.

Lemma red_sub_right (Var Var' : Set)
  (f : Var -> Code Var') (x y : Code Var)
  (xy : red x y) : red (x @ f) (y @ f).
Proof.
  induction xy; repeat rewrite code_sub_ap; simpl; auto.
  apply red_trans with (y @ f); auto.
Qed.
Hint Resolve red_sub_right.

Lemma red_sub (Var Var' : Set)
  (f g : Var -> Code Var') (fg : forall v, red (f v) (g v))
  (x y : Code Var) (xy : red x y) :
  red (code_sub f x) (code_sub g y).
Proof.
  red_to (code_sub g x).
Qed.
Hint Resolve red_sub.

(** ** Abstraction *)

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
  | R => K * R
  | I => K * I
  | K => K * K
  | B => K * B
  | C => K * C
  | S => K * S
  | Y => K * Y
  | V => K * V
  end.

Section red_abs_sub.
  Variable Var Var' : Set.
  Variable b : Var -> option Var'.
  Variable x : Code Var.
  Variable y : Code Var'.
  Let f v := match b v with None => y | Some v' => code_var v' end.

  Lemma red_abs_sub : red (code_abs b x * y) (code_sub f x).
  Proof.
    unfold f; induction x; simpl; auto.
      case (b v);  [intro v'; auto | auto].
    red_to (code_abs b c1 * y * (code_abs b c2 * y)).
    red_to (code_abs b c1 * y * (code_sub f c2)).
  Qed.

  Lemma red_sub_abs : red (code_sub f x) (code_abs b x * y).
  Proof.
    unfold f; induction x; simpl; auto.
      case (b v);  [intro v'; auto | auto].
    red_to (code_abs b c1 * y * (code_abs b c2 * y)).
    red_to (code_abs b c1 * y * (code_sub f c2)).
  Qed.
End red_abs_sub.
Hint Resolve red_abs_sub red_sub_abs.

(* TODO switch to this more efficient lambda abstraction once proof passes *)
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
  | R => K * R
  | I => K * I
  | K => K * K
  | B => K * B
  | C => K * C
  | S => K * S
  | Y => K * Y
  | V => K * V
  end.

Section red_abs_sub'.
  Variable Var Var' : Set.
  Variable b : Var -> option Var'.
  Variable x : Code Var.
  Variable y : Code Var'.
  Let f v := match b v with None => y | Some v' => code_var v' end.
  Lemma red_abs_sub' : red (code_abs' b x * y) (code_sub f x).
  Proof.
    (* TODO
    unfold f; induction x; simpl; auto.
    *)
  Admitted.
End red_abs_sub'.
Hint Resolve red_abs_sub'.

(** Sloppy lambda notation specialized to [Code nat] *)

Definition open {Var : Set} (x : Code Var) : Code (nat + Var) :=
  code_sub (fun v => code_var (inr v)) x.
Definition close {Var : Set} (x : Code (nat + Var)) : Code Var :=
  code_sub (fun v => match v with inr v' => code_var v' | _ => code_top end) x.
Definition make_var (Var : Set) (n : nat) : Code (nat + Var) :=
  code_var (inl n).

Definition code_lambda {Var : Set} (x y : Code (nat + Var)) :
  Code (nat + Var) :=
  let beq_var (v1 v2 : nat + Var) : bool :=
    match v1, v2 with
    | inl n1, inl n2 => beq_nat n1 n2
    | _, _ => false
    end
  in
  match x with
  | code_var v => code_abs (fun v' => if beq_var v v' then None else Some v') y
  | _ => BOT (* TODO implement pattern matching here*)
  end.

(*
Definition code_lambda {Var : Set} (v x : Code (option Var)) : Code Var :=
  match v with
  | code_var n => code_abs (fun v => v) x
  | _ => code_top (* TODO implement pattern matching here*)
  end.
*)

Notation "\ x , y" := (code_lambda x y)%code : code_scope.

(** ** Contexts, convergence, and information ordering *)

Definition code_le {Var : Set} (x y : Code Var) :=
  forall {Var' : Set} (c : Code Var') (f : Var -> Code Var'),
  conv (c * (x @ f)) -> conv (c * (y @ f)).

Notation "x [= y" := (code_le x y)%code : code_scope.
Notation "x [=] y" := (x [= y /\ y [= x)%code : code_scope.

Lemma code_le_refl (Var : Set) (x : Code Var) : x [= x.
Proof.
  unfold code_le; auto.
Qed.
Hint Resolve code_le_refl.

Lemma code_le_trans (Var : Set) (x y z : Code Var) :
  x [= y -> y [= z -> x [= z .
Proof.
  unfold code_le; auto.
Qed.
Hint Resolve code_le_trans.

Lemma code_le_ap_right (Var : Set) (x y y' : Code Var) :
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

Lemma code_le_ap_left (Var : Set) (x x' y : Code Var) :
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

Lemma code_le_ap (Var : Set) (x x' y y': Code Var) :
  code_le x x' -> code_le y y' -> code_le (x * y) (x' * y').
Proof.
  intros Hx Hy.
  apply code_le_trans with (x * y'); auto.
Qed.
Hint Resolve code_le_ap.

Lemma code_le_red_left (Var : Set) (x x' y : Code Var) :
  red x x' -> x [= y -> x' [= y.
Proof.
  unfold code_le; intros Hred Hxy Var' c f Hconv.
  apply Hxy.
  red_to (code_div o c * (x @ f)).
  red_to (code_div o c * (x' @ f)).
  red_to (code_div * (c * (x' @ f))).
Qed.
Hint Resolve code_le_red_left.

Lemma code_le_red_right (Var : Set) (x y y' : Code Var) :
  red y' y -> x [= y -> x [= y'.
Proof.
  unfold code_le; intros Hred Hxy Var' c f Hconv.
  red_to (code_div o c * (y' @ f)).
  red_to (code_div o c * (y @ f)).
  red_to (code_div * (c * (y @ f))).
  apply Hxy; auto.
Qed.
Hint Resolve code_le_red_right.

Lemma code_le_red (Var : Set) (x x' y y' : Code Var) :
  red x x' -> red y' y -> x [= y -> x' [= y'.
Proof.
  intros Hx Hy Hxy.
    apply code_le_red_right with y; auto.
  apply code_le_red_left with x; auto.
Qed.
Hint Resolve code_le_red.

Lemma code_le_abs (Var Var' : Set) (b : Var -> option Var')
  (x y : Code Var) : x [= y -> code_abs b x [= code_abs b y.
Proof.
  intros H; induction x; auto.
Admitted.
Hint Resolve code_le_abs.

Lemma code_le_close {Var : Set} (x y : Code (nat + Var)) :
  x [= y -> close x [= close y.
Proof.
Admitted.
Hint Resolve code_le_close.

Lemma code_le_top (Var : Set) (x : Code Var) : x [= TOP.
Proof.
  unfold code_le; intros Var' c f Hred.
  red_to (code_div o c * TOP).
  red_to (code_div o c * (x @ f)).
  red_to (code_div * (c * (x @ f))).
Qed.
Hint Resolve code_le_top.

(** *** Proving divergence *)

Lemma code_le_bot (Var : Set) (x : Code Var) : BOT [= x.
Proof.
  unfold code_le; intros Var' c f Hred.
  red_to (code_div o c * (x @ f)).
  red_to (code_div o c * BOT).
  red_to (code_div * (c * BOT)).
Qed.
Hint Resolve code_le_bot.

Fixpoint probe {Var : Set} (n : nat) (x : Code Var) : Code Var :=
  match n with
  | 0%nat => x
  | (Succ n')%nat => (probe n' x) * code_top
  end.

Lemma probe_bot_top (Var : Set) : forall n, probe n (@code_bot Var) <> TOP.
Proof.
  intros n; induction n; compute; fold (@probe Var); discriminate.
Qed.

Lemma red_probe_bot_top (Var : Set) :
  forall n, ~ red (probe n (@code_bot Var)) TOP.
Proof.
  intros n H; induction n; auto.
  (* TODO *)
Admitted.

Lemma div_probe_bot (Var : Set) :
  forall n : nat, ~ conv (probe n (@code_bot Var)).
Proof.
  intros n H; inversion H.
Admitted.

(*  TODO

    This is very difficult to prove given the definitions of
    [code], [beta], and [conv].

    See sandbox/hoas.v which adds substitution and
    attempts to strengthen [conv] to get induction to work.
*)

Section Omega.
  Variable Var : Set.
  Let x := make_var Var 0.
  Definition Omega := (\x, x * x) * (\x, x * x).
End Omega.

Lemma code_le_omega_bot (Var : Set) : Omega Var [= BOT.
Proof.
  compute.
  (* TODO *)
Admitted.

Lemma code_eq_omega_bot (Var : Set) : Omega Var [=] BOT.
Proof.
  split ; (apply code_le_omega_bot || auto).
Qed.

(** *** Proving information ordering *)

Lemma code_le_j_left (Var : Set) (x y : Code Var) : x [= x || y.
Proof.
  unfold code_le; intros Var' c f Hred.
  red_to (code_div * (c * (x @ f))).
Qed.
Hint Resolve code_le_j_left.

Lemma code_le_j_right (Var : Set) (x y : Code Var) : y [= x || y.
Proof.
  unfold code_le; intros Var' c f Hred.
  red_to (code_div * (c * (y @ f))).
Qed.
Hint Resolve code_le_j_right.

Lemma code_le_j_ub (Var : Set) (x y z : Code Var) :
  x [= z -> y [= z -> x || y [= z.
Proof.
  unfold code_le; unfold conv; intros Hx Hy Var' c f Hconv.
  (* TODO *)
Admitted.
Hint Resolve code_le_j_ub.

Lemma code_le_join (Var : Set) (x y z : Code Var) :
  x || y [= z <-> x [= z /\ y [= z.
Proof.
  split; intro H.
    split; apply code_le_trans with (x || y); auto.
  destruct H as [Hx Hy]; auto.
Qed.

Lemma code_le_j_idem (Var : Set) (x : Code Var) : x||x [=] x.
Proof.
  split; auto.
Qed.

Lemma code_le_j_sym (Var : Set) (x y : Code Var) : x||y [=] y||x.
Proof.
  split; auto.
Qed.

Lemma code_le_j_assoc (Var : Set) (x y z : Code Var) : x||(y||z) [=] (x||y)||z.
Proof.
  split; auto.
  (* TODO *)
Admitted.

(*
Ltac abstract M x :=
  match m with
  | x => code_ap code_i x
  | code_ap ?M1 ?M2 =>
    let code_ap N1 _ := abstract M1 x in
    let code_ap N2 _ := abstract M2 x in
    code_ap (code_ap (code_ap code_s N1) N2) x
  | _ => code_ap code_k x
  end.

Ltac beta_subs :=
  match goal with
  | beta x y
*)

Lemma code_le_ext (Var : Set) (x x' : Code Var) :
  (forall y, x * y [= x' * y) -> x [= x'.
Proof.
  unfold code_le; intros H Var' c f Hconv.
  (* TODO implement via abstraction algorithm *)
Admitted.
Hint Resolve code_le_ext.

(** *** A head-normalized definition of convergence *)

Fixpoint code_apply {Var : Set} (x : Code Var) (ys : list (Code Var)) :
  Code Var :=
  match ys with
  | nil => x
  | (y ::ys')%list => code_apply (x * y) ys'
  end.

Notation "x ** y" := (code_apply x y)%code : code_scope.

Fixpoint code_tuple {Var : Set} (ys : list (Code Var)) : Code Var :=
  match ys with
  | nil => I
  | (y :: ys')%list => code_tuple ys' o (C * I * y)
  end.

Lemma red_tuple_apply (Var : Set) (ys : list (Code Var)) :
  forall x : Code Var, red (code_tuple ys * x) (x ** ys).
Proof.
  induction ys; simpl; auto; intro x.
  red_to (code_tuple ys * (C * I * a * x)).
  red_to (code_tuple ys * (I * x * a)).
  red_to (code_tuple ys * (x * a)).
Qed.
Hint Resolve red_tuple_apply.

Lemma red_apply_tuple (Var : Set) (ys : list (Code Var)) :
  forall x : Code Var, red (x ** ys) (code_tuple ys * x).
Proof.
  induction ys; simpl; auto; intro x.
  red_to (code_tuple ys * (C * I * a * x)).
  red_to (code_tuple ys * (I * x * a)).
  red_to (code_tuple ys * (x * a)).
Qed.
Hint Resolve red_apply_tuple.

Lemma code_le_apply_easy (Var : Set) (x x' : Code Var) :
  x [= x' ->
  forall (Var' : Set) (ys : list (Code Var')) (f : Var -> Code Var'),
  conv ((x @ f) ** ys) -> conv ((x' @ f) ** ys).
Proof.
  unfold code_le; intros H Var' ys f Hconv.
  red_to (code_div * (code_tuple ys * (x' @ f))).
  apply H.
  red_to (code_div * ((x @ f) ** ys)).
Qed.

Lemma code_le_apply_hard (Var : Set) (x x' : Code Var) :
  (forall (Var' : Set) (ys : list (Code Var')) (f : Var -> Code Var'),
    conv ((x @ f) ** ys) -> conv ((x' @ f) ** ys)) ->
  x [= x'.
Proof.
  unfold code_le; intros H Var' c f Hconv.
  assert (forall (ys : list (Code Var')),
    conv ((x @ f) ** ys) -> conv ((x' @ f) ** ys)) as H'; auto; clear H.
  set (y := x @ f) in *; set (y' := x' @ f) in *.
  inversion Hconv; simpl; auto.
  admit. (* TODO *)
Admitted.

(** ** Observational equivalence *)

Definition code_eq {Var : Set} (x y : Code Var) := x [= y /\ y [= x.
Notation "x [=] y" := (code_eq x y)%code : code_scope.

Lemma code_eq_beta (Var : Set) (x y : Code Var) : beta x y -> x [=] y.
Proof.
  unfold code_eq; intros Hbeta; split.
  assert (Hxy : red x y); auto; apply code_le_red_left with y; auto.
  assert (Hyx : red y x); auto; apply code_le_red_right with y; auto.
Qed.
Hint Resolve code_eq_beta.

Lemma code_eq_ext (Var : Set) (x x' : Code Var) :
  (forall y, x * y [=] x' * y) -> x [=] x'.
Proof.
  unfold code_eq; intro H; split; apply code_le_ext; intro y; apply H.
Qed.
Hint Resolve code_eq_ext.
