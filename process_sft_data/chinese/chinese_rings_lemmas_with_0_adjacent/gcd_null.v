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

Lemma gcd_null : forall a b : S, is_gcd a b O -> a = O /\ b = O.
unfold is_gcd in |- *; intros.
elim H; intros; elim H0; intros; elim H3; intros.
elim H5; intros.
split.
exact H6.
clear H H0 H2 H3 H4 H5 H6.
elim H1; intros; elim H; intros; elim H3; intros; elim H5; intros.
exact H6.
elim H6; intros; elim H7; reflexivity.
elim H6; intros; elim H7; reflexivity.
