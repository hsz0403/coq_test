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

Theorem div_opp : is_ring -> forall a d : S, divide d a -> divide d (Opp a).
Proof.
unfold divide in |- *; intros.
elim H0; intros; elim H2; intros.
split.
exact H1.
clear H0 H2.
elim H; intros; elim H2; intros; elim H5; intros; elim H8; intros.
elim H10; intros; elim (H12 a H3); intros; elim H14; intros.
split.
exact H15.
clear H0 H2 H3 H6 H7 H8 H9 H10 H13 H14 H15 H16.
elim H4; intros.
rewrite H0.
left.
exact (opp_neutral S A Add O Opp H5).
clear H4 H11.
right.
elim H0; intros; elim H3; intros; elim H4; intros.
split.
exact H2.
clear H0 H2 H3 H4.
exists (Opp x).
elim (H12 x H6); intros; elim H2; intros.
split.
exact H3.
clear H3 H4 H5 H6 H12.
rewrite (mult_opp_r H d x H1 H0).
elim H7; reflexivity.
