Require Export Lci.
Require Export misc.
Section groups.
Variable S : Set.
Variable G : S -> Prop.
Variable Add : S -> S -> S.
Variable O : S.
Variable Opp : S -> S.
Definition is_group := intern S G Add /\ associativity S Add /\ neutral S G Add O /\ opposite S G Add O Opp.
End groups.

Lemma opp_unicity : is_group -> forall x y : S, is_opposite S G Add O x y -> y = Opp x.
Proof.
intros.
elim H0; intros; elim H2; intros.
elim H; intros; elim H6; intros; elim H8; intros; elim H9; intros.
elim (H12 y H3); intros; elim H14; clear H H2 H3 H5 H6 H8 H11 H12 H13 H14.
elim (H10 x H1); intros; elim H2; intros; elim H5; intros; elim H8.
clear H H1 H2 H5 H6 H8 H10.
elim (H7 (Opp x) x y).
elim H4; intros; rewrite H; clear H H0 H1 H4 H7.
elim H9; intros; elim (H0 (Opp x) H3); intros.
exact H1.
