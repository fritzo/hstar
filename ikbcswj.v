Inductive code : Set :=
  | I : code
  | K : code
  | B : code
  | C : code
  | W : code
  | S : code
  | J : code
  | BOT : code
  | TOP : code
  | AP : code -> code -> code.

Inductive source : Set :=
  | var: nat -> source
  | app: source -> source -> source
  | abs: var -> source -> source
  | def: var -> source -> source -> source
  | error: source
  | hole: source
  | join: source -> source -> source.

Fixpoint occurs (n : nat) (s : source) :=
  

Fixpoint abstract (n : nat) (s : source) :=
  

Fixpoint compile_ugly (s: source) : code :=
  match s with
    var _ => TOP
  | abs (var n) (app l r) =>
    let nl := compile_ugly (abs (var n) lAP(AP S(compile_

(* these incantations need to be replaced by an abstraction algorithm
Definition I := AP(AP S K)K.
Definition B := AP(AP S(AP K S))K.
Definition C := AP(AP S(AP(AP B S)S))(AP K K).
Definition W := AP(AP C S)I.
Definition B' := AP C B.
Definition Y := AP(AP(AP S B)B').
Definition COMP x y z := AP x(AP y z).
*)

Inductive trace (h:code) (t:code) : Prop :=
  | trace_refl: h = t
  | 

Definition solvable (x : code) : Prop :=

Definition less (x : code) (y : code) :=
  forall f:code, conv(f x) -> conv(f y). 

Lemma less_refl := forall x, less x x.
Proof.
  