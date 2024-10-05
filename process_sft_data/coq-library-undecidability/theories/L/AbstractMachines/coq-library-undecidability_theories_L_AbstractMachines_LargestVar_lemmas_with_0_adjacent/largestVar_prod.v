From Undecidability.L.Datatypes Require Import LProd LNat LTerm.
Fixpoint largestVar (s:term) : nat := match s with var n => n | app s t => max (largestVar s) (largestVar t) | lam s => largestVar s end.

Lemma largestVar_prod X Y `{Rx : registered X} {Ry : registered Y} (w:X*Y): largestVar (enc w) = max (largestVar (enc (fst w))) (largestVar (enc (snd w))).
Proof.
destruct w.
unfold enc.
destruct Rx,Ry.
cbn.
reflexivity.
