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

Theorem div_add : is_ring -> forall a b d : S, divide d a -> divide d b -> divide d (Add a b).
unfold divide in |- *; intros.
split.
elim H0; trivial.
split.
elim H; intros; elim H3; intros; elim H4; intros.
elim H0; intros; elim H9; intros; elim H1; intros; elim H13; intros.
exact (H6 a b H10 H14).
elim H; intros; elim H3; intros; elim H4; intros; elim H5; intros.
elim H7; intros; elim H9; intros; elim H11; intros; elim H14; intros.
clear H H2 H3 H4 H5 H7 H8 H9 H10 H11 H12 H14 H15 H16.
elim H0; intros; elim H2; intros; clear H H0 H2.
elim H1; intros; elim H0; intros; clear H H0 H1.
elim H4; intros.
rewrite H.
elim (H17 b H2); intros.
rewrite H1.
exact H5.
elim H5; intros.
rewrite H0.
elim (H17 a H3); intros.
rewrite H1.
exact H4.
clear H2 H3 H4 H5 H17.
right.
elim H; intros; elim H2; intros; elim H3; intros; clear H H2 H3.
elim H0; intros; elim H2; intros; elim H3; intros; clear H H0 H2 H3.
split.
exact H1.
clear H1.
exists (Add x x0).
split.
exact (H6 x x0 H4 H7).
elim (H13 d x x0); intros.
clear H4 H6 H7 H13.
rewrite H0.
clear H H0.
elim H5; elim H8; reflexivity.
