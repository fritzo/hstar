
Inductive code :=
  | _S : code
  | _K : code
  | _R : code
  | _J : code
  | _AP : code -> code -> code
  | _Join : (nat -> code) -> code.
(* FIXME [_Join] this makes comprehension axiom messy *)

Infix "*" := _AP : code_scope.
Bind Scope code_scope with code.
Delimit Scope code_scope with code.
Open Scope code_scope.

Parameter Ob : Set.
Parameter AP : Ob -> Ob -> Ob.
Parameter Join : (Ob -> Prop) -> Ob.

Parameter eval : code -> Ob.
Notation "[ x ]" := (eval x) : Ob_scope.
Infix "*" := AP : Ob_scope.
Bind Scope Ob_scope with Ob.
Delimit Scope Ob_scope with Ob.
Open Scope Ob_scope.

Axiom eval_AP : forall (x y : code), [x * y] = [x] * [y].

Definition S := [_S].
Definition K := [_K].
Definition R := [_R].
Definition J := [_J].
