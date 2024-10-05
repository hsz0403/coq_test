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

Lemma mult_opp_opp : is_ring -> forall x y : S, A x -> A y -> Mult (Opp x) (Opp y) = Mult x y.
Proof.
intros.
elim H; intros; elim H3; intros; elim H4; intros; elim H5; intros.
elim H7; intros; elim H9; intros; elim H11; intros; elim (H15 x H0); intros.
elim H17; intros; clear H2 H3 H5 H6 H7 H9 H10 H11 H12 H13 H14 H15 H16 H17 H19.
rewrite (mult_opp_r H (Opp x) y H18 H1).
rewrite (mult_opp_l H x y H0 H1).
symmetry in |- *.
exact (opp_opp S A Add O Opp H4 (Mult x y) (H8 x y H0 H1)).
