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

Lemma gcd_unicity_apart_unities : is_unitary_commutative_ring -> integrity -> forall a b d1 d2 : S, is_gcd a b d1 -> is_gcd a b d2 -> exists x : S, inversible S Mult I x /\ A x /\ d2 = Mult d1 x.
intros.
elim H2; intros; elim H4; intros; elim H1; intros; elim H8; intros.
elim (H6 d1 H7 H9); intros; elim H12; intros; elim H14; intros.
exists I.
unfold inversible in |- *.
elim H; intros; elim H17; intros; elim H19; intros.
split.
exists I.
exact (H21 I H20).
split.
exact H20.
elim (gcd_null a b); intros.
rewrite H15.
rewrite (gcd_null2 H16 d1).
elim (mult_O H16 I); intros.
symmetry in |- *; exact H25.
exact H20.
pattern O at 1 in |- *; elim H22; elim H23; exact H1.
elim H15; exact H2.
elim H15; intros; elim H17; intros.
exists x.
elim H; intros; elim H20; intros.
split.
apply (inv_com S Mult I x H21).
elim H1; intros; elim H24; intros; elim (H26 d2 H3 H5); intros.
elim H28; intros; elim H30; intros.
elim H16; exact H31.
elim H31; intros; elim H33; intros.
exists x0.
elim H34; intro; clear H35.
elim H18; intro; intro.
rewrite H36.
elim H; intros H37 H38; elim H37; intros H39 H40; elim H40; intros H41 H42.
elim H42; intros H43 H44; elim H44; intros H45 H46; elim (H45 d1 x x0); intros.
elim H34; intros.
apply (simplification_integrity H H0 d1 (Mult x x0) H11 (H43 x x0 H35 H48) H16).
symmetry in |- *; exact H47.
exact H18.
