Require Export Lci.
Require Export misc.
Require Export groups.
Require Export Compare_dec.
Section ring.
Variable S : Set.
Variable A : S -> Prop.
Variable Add Mult : S -> S -> S.
Variable O I : S.
Variable Opp : S -> S.
Variable v : S -> nat.
Definition is_ring := commutativity S Add /\ is_group S A Add O Opp /\ intern S A Mult /\ associativity S Mult /\ distributivity S Add Mult.
Definition integrity := forall a b : S, Mult a b = O -> {a = O} + {b = O}.
Definition is_unitary_commutative_ring := is_ring /\ commutativity S Mult /\ neutral S A Mult I.
Definition divide (a b : S) := A a /\ A b /\ (b = O \/ a <> O /\ (exists q : S, A q /\ b = Mult a q)).
Definition is_gcd (a b d : S) := divide d a /\ divide d b /\ (forall q : S, divide q a -> divide q b -> divide q d).
End ring.

Theorem div_mult : is_ring -> forall a b d : S, divide d a -> A b -> divide d (Mult a b).
Proof.
unfold divide in |- *; intros.
elim H0; intros.
split.
exact H2.
clear H0 H2.
elim H; intros; elim H2; intros; elim H5; intros; elim H7; intros.
clear H0 H2 H4 H5 H7 H9.
elim H3; intros.
split.
exact (H6 a b H0 H1).
clear H0 H3.
elim H2; intros.
rewrite H0.
elim (mult_O H b H1); intros.
rewrite H4.
left; reflexivity.
clear H H2.
right.
elim H0; intros; elim H2; intros.
split.
exact H.
exists (Mult x b).
elim H3; intros.
split.
exact (H6 x b H4 H1).
rewrite (H8 d x b).
elim H5; reflexivity.
