From Undecidability.L.Datatypes Require Import LProd LNat LTerm.
Fixpoint largestVar (s:term) : nat := match s with var n => n | app s t => max (largestVar s) (largestVar t) | lam s => largestVar s end.

Lemma largestVar_prod X Y `{Rx : registered X} {Ry : registered Y} (w:X*Y): largestVar (enc w) = max (largestVar (enc (fst w))) (largestVar (enc (snd w))).
Proof.
destruct w.
unfold enc.
destruct Rx,Ry.
cbn.
Admitted.

Lemma largestVar_nat (n:nat): largestVar (enc n) <= 1.
Proof.
unfold enc,registered_nat_enc.
induction n;cbn in *.
Admitted.

Lemma largestVar_size s : largestVar s <= size s.
Proof.
Admitted.

Lemma largestVar_term (s:term): largestVar (enc s) <= 2.
Proof.
unfold enc,registered_term_enc.
induction s;cbn -[max] in *.
1:rewrite largestVar_nat.
all:try Lia.lia.
