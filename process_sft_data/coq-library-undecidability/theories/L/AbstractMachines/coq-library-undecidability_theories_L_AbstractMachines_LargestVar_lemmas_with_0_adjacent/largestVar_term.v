From Undecidability.L.Datatypes Require Import LProd LNat LTerm.
Fixpoint largestVar (s:term) : nat := match s with var n => n | app s t => max (largestVar s) (largestVar t) | lam s => largestVar s end.

Lemma largestVar_term (s:term): largestVar (enc s) <= 2.
Proof.
unfold enc,registered_term_enc.
induction s;cbn -[max] in *.
1:rewrite largestVar_nat.
all:try Lia.lia.
