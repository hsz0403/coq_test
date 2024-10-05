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

Lemma mult_opp_l : is_ring -> forall x y : S, A x -> A y -> Mult (Opp x) y = Opp (Mult x y).
intros.
elim H; intros; elim H3; intros; elim H4; intros; elim H5; intros.
elim H7; intros; elim H9; intros; elim H11; intros; elim (H15 x H0); intros.
elim H17; intros; elim H19; intros.
clear H2 H3 H5 H6 H7 H9 H10 H11 H12 H14 H15 H16 H17 H19.
apply (opp_unicity S A Add O Opp H4 (Mult x y) (Mult (Opp x) y)).
unfold is_opposite in |- *; split.
exact (H8 x y H0 H1).
split.
exact (H8 (Opp x) y H18 H1).
elim (mult_O H y H1); intros; elim H3; clear H H0 H1 H2 H3 H4 H8 H18.
pattern O at 1 in |- *; elim H20; elim H21; clear H20 H21.
elim (H13 x (Opp x) y); intros; rewrite H; clear H H0.
elim (H13 (Opp x) x y); intros; rewrite H; auto.
