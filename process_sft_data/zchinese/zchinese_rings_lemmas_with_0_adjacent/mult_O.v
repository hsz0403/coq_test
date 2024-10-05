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

Lemma mult_O : is_ring -> forall x : S, A x -> Mult x O = O /\ Mult O x = O.
Proof.
intros.
elim H; intros; elim H2; intros; elim H3; intros; elim H4; intros.
elim H6; intros; elim H8; intros; elim H10; intros; elim H13; intros.
clear H2 H4 H5 H6 H8 H9 H10 H11 H13 H14.
split.
apply (regular_l S A Add O Opp H3 (Mult x O) O (H7 x O H0 H15) H15 (Mult x O) (H7 x O H0 H15)).
elim (H16 (Mult x O) (H7 x O H0 H15)); intros; rewrite H2.
elim (H12 x O O); intros; elim H6.
elim (H16 O H15); intros; rewrite H8; reflexivity.
apply (regular_l S A Add O Opp H3 (Mult O x) O (H7 O x H15 H0) H15 (Mult O x) (H7 O x H15 H0)).
elim (H16 (Mult O x) (H7 O x H15 H0)); intros; rewrite H2.
elim (H12 O O x); intros; elim H5.
elim (H16 O H15); intros; rewrite H8; reflexivity.
