Inductive code : Set :=
  | S : code
  | K : code
  | J : code
  | AP : code -> code -> code.

(* TODO translate this knowledge from object language to coq *) 
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

Inductive red : code -> code -> Prop :=
  | red_refl: forall x, red x x
  | red_trans: forall x y z, red x y -> red y z -> red x z
  | red_s: forall x y z, red (AP(AP(AP S x)y)z) (AP(AP x z)(AP y z))
  | red_k: forall x y, red (AP(AP K x)y) x
  | red_j_1: forall x y, red (AP(AP J x)y) x
  | red_j_2: forall x y, red (AP(AP J x)y) y
  | red_ap_1: forall x y z, red x y -> red (AP z x) (AP z y)
  | red_ap_2: forall x y z, red x y -> red (AP z x) (AP z y).

Inductive code_conv : code -> Prop :=
  | code_conv_red: forall x, red x TOP -> code_conv x
  | code_conv_top: forall x, code_conv (AP x TOP) -> code_conv x.

Definition code_le (x : code) (y : code) : Prop :=
  forall f : code, code_conv (AP f x) -> code_conv (AP f y). 

Lemma less_refl := forall x, less x x.
Proof.
  
