theory Skj
imports Main
begin

datatype ob = S | K | J | APP "ob" "ob"

definition I :: ob where
  I_def: "I = APP(APP S K)K"

definition join :: "ob \<Rightarrow> ob \<Rightarrow> ob" where
  join_def: "join x y = APP(APP J x)y"

(*
fun app :: "ob list \<Rightarrow> ob" where
"app [x] = x" |
"app (x # xs) = "
*)

axiomatization
  EQ :: "ob \<Rightarrow> ob \<Rightarrow> bool" where
  eq_refl: "EQ x x" and
  eq_sym: "EQ x y \<Longrightarrow> EQ y x" and
  eq_trans: "EQ x y \<and> EQ y z \<Longrightarrow> EQ x z" and
  eq_s: "EQ (APP(APP(APP S x)y)z) (APP(APP x z)(APP y z))" and
  eq_k: "EQ (APP(APP K x)y) x"

axiomatization
  LE :: "ob \<Rightarrow> ob \<Rightarrow> bool" where
  less_refl: "EQ x y \<Longrightarrow> LE x y" and
  less_antisym: "LE x y \<and> LE y x \<Longrightarrow> EQ x y" and
  less_trans: "LE x y \<and> LE y z \<Longrightarrow> LE x z" and
  j: "LE x (APP(APP J x)y)" and
  j_sym: "EQ(join x y)(join y x)"

lemma i: "EQ (APP I x) x"
apply(auto)
done

end
