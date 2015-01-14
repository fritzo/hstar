
(** printing TOP $\top$ *)
(** printing BOT $\bot$ *)

(** printing * $\ensuremath{\ast}$ *)
(** printing )* $\ensuremath{)\ast}$ *)
(** printing *( $\ensuremath{\ast(}$ *)
(** printing )*( $\ensuremath{)\ast(}$ *)

(** printing (+) $\ensuremath{\oplus}$ *)
(** printing [= $\ensuremath{\sqsubseteq}$ *)
(** printing [!= $\ensuremath{\not\sqsubseteq}$ *)
(** printing =] $\ensuremath{\sqsupseteq}$ *)

Reserved Notation "x * y" (at level 40, left associativity).
Reserved Notation "x ** y" (at level 40, left associativity).
Reserved Notation "x 'o' y" (at level 30, right associativity).
Reserved Notation "x || y" (at level 50, left associativity).
Reserved Notation "x (+) y" (at level 45, no associativity).
Reserved Notation "x --> y" (at level 55, right associativity).
Reserved Notation "x @ f" (at level 55, right associativity).
Reserved Notation "x [= y" (at level 60, no associativity).
Reserved Notation "x [=] y" (at level 60, no associativity).
Reserved Notation "x [!= y" (at level 60, no associativity).
Reserved Notation "x ->> y" (at level 60, no associativity).
Reserved Notation "\ x , y" (at level 58, right associativity).
Reserved Notation "\\ x , y ; z" (at level 59, right associativity).

Reserved Notation "[ x ]".
