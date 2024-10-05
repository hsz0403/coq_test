Require Export Arith.
Require Export ArithRing.
Require Export Omega.
Unset Standard Proposition Elimination Names.

Lemma plus_minus_lemma1 : forall (y x:nat),(x+y-y=x).
induction y;intros;rewrite plus_comm;simpl.
auto with arith.
rewrite plus_comm.
apply IHy.
