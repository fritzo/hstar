(** * This follows the axiomatic treatment of reals
    in the Coq standard library. *)

(** ** Axioms *)

Parameter Ob : Set.
Parameter BOT : Ob.
Parameter TOP : Ob.
Parameter I : Ob.
Parameter K : Ob.
Parameter F : Ob.
Parameter B : Ob.
Parameter C : Ob.
Parameter S : Ob.
Parameter R : Ob.
Parameter J : Ob.
Parameter AP : Ob -> Ob -> Ob.
Parameter LESS : Ob -> Ob -> Prop.
Parameter Join : (Ob -> Prop) -> Ob.

Notation "x * y" := (AP x y) (at level 40, left associativity) : Ob_scope.

Open Scope Ob_scope.
Delimit Scope Ob_scope with Ob.
Bind Scope Ob_scope with Ob.

Notation "x 'o' y" := (B * x * y) (at level 30, right associativity) : Ob_scope.
Notation "x || y" := (J * x * y) (at level 50, left associativity) : Ob_scope.
Notation "x (+) y" := (R * x * y) (at level 45, no associativity) : Ob_scope.
Notation "x [= y" := (LESS x y) (at level 60, no associativity) : Ob_scope.

Axiom TOP_def: forall x, x [= TOP.
Axiom BOT_def: forall x, BOT [= x.
Axiom I_beta: forall x, I*x = x.
Axiom K_beta: forall x y, K*x*y = x.
Axiom F_beta: forall x y, F*x*y = y.
Axiom B_beta: forall x y z, B*x*y*z = x*(y*z).
Axiom C_beta: forall x y z, C*x*y*z = x*z*y.
Axiom S_beta: forall x y z, S*x*y*z = x*z*(y*z).
Axiom J_ap: forall x y z, (x||y)*z = x*z || y*z.
Axiom J_left: forall x y, x||y [= x.
Axiom J_right: forall x y, x||y [= y.
Axiom J_lub: forall x y z, x [= z -> y [= z -> x||y [= z.
Axiom R_ap: forall x y z, (x(+)y)*z = x*z (+) y*z.
Axiom R_idem: forall x, x(+)x = x.
Axiom R_sym: forall x y, x(+)y = y(+)x.
Axiom R_sym_sym: forall w x y z, (w(+)x) (+) (y(+)z) = (y(+)x) (+) (w(+)z).
Axiom R_subconvex: forall x y z, x [= z -> y [= z -> x(+)y [= z.
Axiom R_supconvex: forall x y z, z [= x -> z [= x -> z [= x(+)y.
Axiom LESS_refl: forall x, x [= x.
Axiom LESS_antisym: forall x y, x [= y -> y [= x -> x = y.
Axiom LESS_trans: forall x y z, x [= y -> y [= z -> x [= z.
Axiom LESS_AP: forall x x' y y', x [= x' -> y [= y' -> x*y [= x'*y'.

Definition is_upper_bound (s : Ob -> Prop) (x : Ob) : Prop :=
  forall y, s y -> y [= x.

Definition is_lub (s : Ob -> Prop) (x : Ob) : Prop :=
  is_upper_bound s x /\ forall y, is_upper_bound s y -> x [= y.

Axiom Join_lub: forall s, is_lub s (Join s).

(** ** Global properties *)

Axiom consistency: ~ TOP [= BOT.

Axiom extensionality: forall f g, (forall x, f * x = g * x) -> f = g.

Theorem completeness: forall s, exists x, is_lub s x.
Proof.
  intros s.
  exists (Join s).
  apply Join_lub.
Qed.

(** ** Definability and accessibility *)

Inductive definable : Ob -> Prop :=
  | S_definable: definable S
  | K_definable: definable K
  | R_definable: definable R
  | J_definable: definable J
  | AP_definable x y: definable x -> definable y -> definable (x*y).

Axiom accessibility: forall x : Ob, x = Join (fun y => y [= x /\ definable y).