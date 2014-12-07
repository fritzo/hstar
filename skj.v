Inductive code : Set :=
  | S : code
  | K : code
  | J : code
  | AP : code -> code -> code.

Definition I := AP(AP S K)K.
Definition B := AP(AP S(AP K S))K.
Definition C := AP(AP S(AP(AP B S)S))(AP K K).
Definition CI := AP C I.
Definition W := AP(AP C S)I.
Definition B' := AP C B.
Definition Y := AP(AP(AP S B)B')(AP W I).
Definition COMP x y z := AP x(AP y z).
Definition JOIN x y := AP(AP J x)y.
Definition TOP := AP Y J.
Definition DIV := AP Y(JOIN I (AP CI TOP)). 

Inductive red (h:code) (t:code) : Prop :=
  | red_refl: h = t
  | red_left: 

Definition solvable x := red (AP DIV x) TOP.

Definition less (x : code) (y : code) :=
  forall f:code, conv(f x) -> conv(f y). 

Lemma less_refl := forall x, less x x.
Proof.
  