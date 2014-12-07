(* Quotient examples.

Cohen (2013) assumes decidable equivalence relation,
and represents quotients of T:Type as (here formalized)
  \/Q:Type. (pi:T->Q) * (repr:Q->T) * (forall q:Q, repr(pi q) = q).

@incollection{cohen2013pragmatic,
  title={Pragmatic quotient types in coq},
  author={Cohen, Cyril},
  booktitle={Interactive Theorem Proving},
  pages={213--228},
  year={2013},
  publisher={Springer},
  url={http://perso.crans.org/cohen/papers/quotients.pdf},
}

*)

