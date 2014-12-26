
Inductive code : Set :=
  | _S : code
  | _K : code
  | _R : code
  | _J : code
  | _AP : code -> code -> code.

Inductive limit : Set := sup : (nat -> code) -> limit.
Definition just (x : code) := sup (fun _ => x).

(* TODO change this to a definition *)
Parameter ap_join : limit -> limit -> limit.

Infix "*" := ap_join : limit_scope.
Bind Scope limit_scope with limit.
Delimit Scope limit_scope with limit.
Open Scope limit_scope.

Parameter Ob : Set.
Parameter AP : Ob -> Ob -> Ob.
Parameter eval : limit -> Ob.
Notation "[ x ]" := (eval x) : Ob_scope.
Infix "*" := AP : Ob_scope.
Bind Scope Ob_scope with Ob.
Delimit Scope Ob_scope with Ob.
Open Scope Ob_scope.

Axiom eval_AP : forall (x y : limit), [x * y] = [x] * [y].

Definition S := [just _S].
Definition K := [just _K].
Definition R := [just _R].
Definition J := [just _J].
