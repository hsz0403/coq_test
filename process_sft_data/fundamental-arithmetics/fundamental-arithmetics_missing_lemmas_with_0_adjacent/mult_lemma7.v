Require Export Arith.
Require Export ArithRing.
Require Export Omega.
Unset Standard Proposition Elimination Names.

Lemma mult_lemma7 : forall (x y z t:nat),x*y*(z*t)=z*(x*y*t).
intros.
ring.
