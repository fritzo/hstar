
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

Reserved Notation "[ x ]".

(** We combine replacement with comprehension as [(m for x : s if p)],
    which is more flexible than comprehension alone [{x : s & p}].
    This will be especially useful for constructing [Join]s.  *)

Notation "( m 'for' x1 : t1 )" :=
  (fun x1 : t1 => m)
  (at level 0, x1 at level 99) : type_scope.
Notation "( m 'for' x1 : t1 'if' t2 )" :=
  (fun x : {x1 : t1 & t2} => match x with existT x1 _ => m end)
  (at level 0, x1 at level 99) : type_scope.
Notation "( m 'for' x1 : t1 'if' t2 'if' t3 )" :=
  (fun x : {x1 : t1 & t2 & t3} => match x with existT2 x1 _ _ => m end)
  (at level 0, x1 at level 99) : type_scope.
Notation "( m 'for' x1 : t1 'for' x2 : t2 )" :=
  (fun x : t1 * t2 => match x with (x1, x2) => m end)
  (at level 0, x1 at level 99, x2 at level 99) : type_scope.
Notation "( m 'for' x1 : t1 'for' x2 : t2 'if' t3 )" :=
  (fun x : sigT (fun x12 : t1 * t2 => let (x1, x2) := x12 in t3) =>
  match x with existT (x1, x2) _ => m end)
  (at level 0, x1 at level 99, x2 at level 99) : type_scope.
Notation "( m 'for' x1 : t1 'for' x2 : t2 'if' t3 )" :=
  (fun x : sigT (fun x12 : t1 * t2 => let (x1, x2) := x12 in t3) =>
  match x with existT (x1, x2) _ => m end)
  (at level 0, x1 at level 99, x2 at level 99) : type_scope.
Notation "( m 'for' x1 : t1 'for' x2 : t2 'if' t3 'if' t4 )" :=
  (fun x : sigT2 (fun x12 : t1 * t2 => let (x1, x2) := x12 in t3)
                 (fun x12 : t1 * t2 => let (x1, x2) := x12 in t4) =>
  match x with existT2 (x1, x2) _ _ => m end)
  (at level 0, x1 at level 99, x2 at level 99) : type_scope.
