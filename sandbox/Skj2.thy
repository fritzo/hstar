theory Skj2
imports Main Complete_Lattices
begin

notation
  less_eq (infix "\<sqsubseteq>" 50) and
  less (infix "\<sqsubset>" 50)

class ordered_combinatory_algebra = lattice + Sup + bot + top +
  assumes Sup_upper: "x \<in> A \<Longrightarrow> x \<sqsubseteq> Sup A"
     and Sup_least: "(\<And>x. x \<in> A \<Longrightarrow> x \<sqsubseteq> z) \<Longrightarrow> Sup A \<sqsubseteq> z"

datatype ob = S | K | J | APP ob ob



end
