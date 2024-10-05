Require Export Lci.
Require Export misc.
Require Export Arith.
Require Export Nat_complements.
Require Export groups.
Require Export rings.
Require Export Zbase.
Require Export Z_succ_pred.
Require Export Zadd.
Fixpoint multpos (x2 : Z) (n : nat) {struct n} : Z := match n with | O => x2 | S n0 => addZ (multpos x2 n0) x2 end.
Fixpoint multneg (x2 : Z) (n : nat) {struct n} : Z := match n with | O => oppZ x2 | S n0 => addZ (multneg x2 n0) (oppZ x2) end.
Definition multZ (x1 x2 : Z) := match x1 with | OZ => OZ | pos n => multpos x2 n | neg n => multneg x2 n end.

Lemma tech_integ_negZ : forall (n : nat) (x : Z), multZ (neg n) x = OZ -> x = OZ.
intros n x; elim x.
reflexivity.
intros n0; rewrite (tech_mult_neg_posZ n n0); intros.
absurd (neg (n * n0 + (n + n0)) = OZ).
discriminate.
exact H.
intros n0; rewrite (tech_mult_neg_negZ n n0); intros.
absurd (pos (n * n0 + (n + n0)) = OZ).
discriminate.
exact H.
