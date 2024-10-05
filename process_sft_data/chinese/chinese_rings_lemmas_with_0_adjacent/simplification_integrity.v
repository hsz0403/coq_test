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

Lemma simplification_integrity : is_unitary_commutative_ring -> integrity -> forall a x : S, A a -> A x -> a <> O -> Mult a x = a -> x = I.
intros.
elim H; intros; elim H5; intros; elim H6; intros; elim H8; intros.
elim H11; intros; elim H12; intros; elim H14; intros; elim H16; intros.
elim H18; intros.
clear H6 H8 H9 H12 H13 H14 H15 H16 H17 H18 H19 H21.
rewrite (opp_opp S A Add O Opp H11 x H2).
symmetry in |- *; apply (opp_unicity S A Add O Opp H11 (Opp x) I).
elim (H22 x H2); intros; elim H8; intros; elim H10; intros.
apply (opp_com S A Add O H7 (Opp x) I H9 H13).
clear H6 H8 H12 H13.
elim (H0 a (Add (Opp x) I)); intros.
elim H3.
exact a0.
exact b.
elim (H20 a (Opp x) I); intros.
rewrite H8.
elim (H14 a H1); intros.
rewrite H12.
clear H6 H8 H9 H12 H13 H14.
rewrite (mult_opp_r H5 a x H1 H2).
rewrite H4.
elim (H22 a H1); intros; elim H8; intros; elim H12; intros; exact H14.
