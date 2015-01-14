
(** printing TOP $\pmb\top$ *)
(** printing BOT $\pmb\bot$ *)

(** remove printing * *)
(** printing * $\cdot$ *)
(** printing )* $)\cdot$ *)
(** printing *( $\cdot($ *)
(** printing )*( $)\cdot($ *)

(** printing (+) $\oplus$ *)
(** printing || $\parallel$ *)
(** printing [= $\sqsubseteq$ *)
(** printing [!= $\not\sqsubseteq$ *)
(** printing =] $\sqsupseteq$ *)
(** printing == $\equiv$ *)

Reserved Notation "x * y" (at level 40, left associativity).
Reserved Notation "x ** y" (at level 40, left associativity).
Reserved Notation "x 'o' y" (at level 30, right associativity).
Reserved Notation "x || y" (at level 50, left associativity).
Reserved Notation "x (+) y" (at level 45, no associativity).
Reserved Notation "x --> y" (at level 55, right associativity).
Reserved Notation "x @ f" (at level 55, right associativity).
Reserved Notation "x [= y" (at level 60, no associativity).
Reserved Notation "x [!= y" (at level 60, no associativity).
Reserved Notation "x == y" (at level 60, no associativity).
Reserved Notation "x ->> y" (at level 60, no associativity).
Reserved Notation "\ x , y" (at level 58, right associativity).
Reserved Notation "\\ x , y ; z" (at level 59, right associativity).

Reserved Notation "[ x ]".
