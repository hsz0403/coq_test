From Undecidability.L.Datatypes Require Import LProd LNat LTerm.
Fixpoint largestVar (s:term) : nat := match s with var n => n | app s t => max (largestVar s) (largestVar t) | lam s => largestVar s end.

Lemma largestVar_size s : largestVar s <= size s.
Proof.
induction s;cbn;Lia.lia.
