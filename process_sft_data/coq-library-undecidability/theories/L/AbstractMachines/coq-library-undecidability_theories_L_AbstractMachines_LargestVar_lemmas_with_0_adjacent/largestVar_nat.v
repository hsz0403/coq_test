From Undecidability.L.Datatypes Require Import LProd LNat LTerm.
Fixpoint largestVar (s:term) : nat := match s with var n => n | app s t => max (largestVar s) (largestVar t) | lam s => largestVar s end.

Lemma largestVar_nat (n:nat): largestVar (enc n) <= 1.
Proof.
unfold enc,registered_nat_enc.
induction n;cbn in *.
all:Lia.lia.
