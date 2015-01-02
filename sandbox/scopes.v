
Print Visibility.

Check fun (x y : nat) => x * y.
(* This fails:
Check fun (x y : Type) => x * y.
*)
Check fun (x y : Type) => (x * y)%type.
Check fun (x y : Type) => x * y -> x.

Inductive A : Set := | a_leaf : A | a_pair : A -> A -> A.
Notation "x * y" := (a_pair x y) : A_scope.
Bind Scope A_scope with A.


(*--------------------------------------------------------------------------*)

Inductive Ob : Set :=
  | S : Ob
  | K : Ob
  | AP : Ob -> Ob -> Ob.

Notation "x * y" := (AP x y) (at level 40, left associativity) : Ob_scope.

Open Scope Ob_scope.
Delimit Scope Ob_scope with Ob.
Bind Scope Ob_scope with Ob.

Print Visibility.

Check fun (x y : Type) => (x * y)%type.
Check fun (x y : Type) => x * y -> x.
Check fun (x y : nat) => (x * y)%nat.


Inductive Part : Set :=
  | OB : Ob -> Part
  | HOLE : Part
  | APP : Part -> Part -> Part.

Notation "x * y" := (APP x y) (at level 40, left associativity) : Part_scope.
Notation "[ x ]" := (OB x) (at level 40) : Part_scope.

Open Scope Part_scope.
Delimit Scope Part_scope with Part.
Bind Scope Part_scope with Part.

Print Visibility.

Check fun (x y : Ob) => (x * y)%Ob.

Check [S].
Check HOLE * HOLE.
Check (S * S)%Ob.
Check [S * S].
Check [S * K] * [K] * HOLE.
Check [(S * K)%Ob] * [K] * HOLE.
Check [S * K] * [K] * HOLE.
