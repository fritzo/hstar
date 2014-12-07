Inductive term : Set :=
 | S : term
 | K : term
 | J : term
 | APP : term -> term -> term.

Definition I := APP(APP S K)K.
(*
Definition B :=
Definition Y := 
*)

Fixpoint normal (t : term) : Prop :=
 match t with
   S => True
 | APP S x => normal x
 | APP(APP S x)y => normal x /\ normal y
 | K => True
 | APP K x => normal x
 | _ => False
 end.

Theorem i_normal : normal I.
simpl; auto.
Qed.

Fixpoint beta_step (t : term) : option term :=
 match t with
   APP(APP(APP S x)y)z => Some(APP(APP x z)(APP y z))
 | APP(APP K x)y => Some x
 | _ => None
end.

(* this does not work
Theorem beta_normal:
  forall x : term, beta_step x = None -> normal x.
destruct x.
destruct 1; reflexivity.
destruct 1; reflexivity.
destruct 1.
destruct x1.
*)

Inductive trace : Set :=