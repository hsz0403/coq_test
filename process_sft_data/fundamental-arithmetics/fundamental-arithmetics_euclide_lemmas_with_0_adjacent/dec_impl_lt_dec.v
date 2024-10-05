Require Import missing.
Require Import division.
Require Import Wf_nat.
Unset Standard Proposition Elimination Names.
Definition quotient_euclide (a b:nat)(H:(b<>O)) := let (q,_) := (euclide a b H) in q.
Definition remainder_euclide (a b:nat)(H:(b<>O)) := let (_,e0) := (euclide a b H) in let (r,_) := e0 in r.

Lemma dec_impl_lt_dec : forall (P:nat->Prop),(forall (n:nat),{(P n)}+{~(P n)})->(forall (m:nat),{n:nat | (n<m)/\(P(n))}+{(forall (n:nat),(n<m)->~(P n))}).
intros.
induction m.
right;intros;inversion H0.
case (H m);intro.
left;exists m;split;try (auto with arith).
case IHm;intro.
elim s;intro n0;intro.
left;exists n0;split;[omega | tauto].
right;intros.
inversion H0;trivial.
apply n0;omega.
