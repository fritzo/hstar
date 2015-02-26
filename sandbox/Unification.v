
Inductive term : Set :=
  | term_bot : term
  | term_join : term -> term -> term
  | term_app : term -> term -> term
  | term_var : nat -> term
  | term_lambda : term -> term.
Hint Constructors term.

Inductive type : Set :=
  | type_var : nat -> type
  | type_exp : type -> type -> type
  | type_error : type.
Hint Constructors type.

Inductive typed : Set :=
  | typed_bot : type -> typed
  | typed_join : typed -> typed -> type -> typed
  | typed_app : typed -> typed -> type -> typed
  | typed_var : nat -> type -> typed
  | typed_lambda : typed -> type -> typed.
Hint Constructors term.

Definition get_fresh (fresh : nat) : type * nat :=
  (type_var fresh, Datatypes.S fresh).

Fixpoint annotate' (t : term) (fresh : nat) : typed * nat :=
  match t with
  | term_bot =>
      let (a, fresh) := get_fresh fresh in
      (typed_bot a, fresh)
  | term_join x y =>
      let (tx, fresh) := annotate' x fresh in
      let (ty, fresh) := annotate' y fresh in
      let (a, fresh) := get_fresh fresh in
      (typed_join tx ty a, fresh)
  | term_app x y =>
      let (tx, fresh) := annotate' x fresh in
      let (ty, fresh) := annotate' y fresh in
      let (a, fresh) := get_fresh fresh in
      (typed_app tx ty a, fresh)
  | term_var v =>
      let (a, fresh) := get_fresh fresh in
      (typed_var v a, fresh)
  | term_lambda x =>
      let (tx, fresh) := annotate' x fresh in
      let (a, fresh) := get_fresh fresh in
      (typed_lambda tx a, fresh)
  end.

Definition annotate (t : term) := let (t', _) := annotate' t 0 in t'.

Definition typed_map (f : type -> type) : typed -> typed :=
  fix m t :=
  match t with
  | typed_bot a => typed_bot (f a)
  | typed_join x y a => typed_join (m x) (m y) (f a)
  | typed_app x y a => typed_app (m x) (m y) (f a)
  | typed_var v a => typed_var v (f a)
  | typed_lambda x a => typed_lambda (m x) (f a)
  end.

(* TODO How to define a terminating unification function
   when unification can have exponential complexity? *)
