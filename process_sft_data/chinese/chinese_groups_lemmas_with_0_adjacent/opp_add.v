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

Lemma opp_add : is_group -> commutativity S Add -> forall x y : S, G x -> G y -> Opp (Add x y) = Add (Opp x) (Opp y).
Proof.
intros; symmetry in |- *; apply (opp_unicity H (Add x y) (Add (Opp x) (Opp y))).
unfold is_opposite in |- *; split.
elim H; intros; apply (H3 x y H1 H2).
split.
elim H; intros; elim H4; intros; elim H6; intros; clear H4 H5 H6 H7.
elim (H8 x H1); intros; elim H5; intros; clear H4 H5 H7.
elim (H8 y H2); intros; elim H5; intros.
apply (H3 (Opp x) (Opp y) H6 H7).
elim H; intros; elim H4; intros; clear H3 H4 H6.
rewrite (add_add H0 H5 x y (Opp x) (Opp y)).
rewrite (add_add H0 H5 (Opp x) (Opp y) x y); clear H5.
elim H; intros; elim H4; intros; elim H6; intros.
elim (H8 x H1); intros; elim H10; intros; elim H12; intros.
rewrite H13; rewrite H14.
clear H H0 H1 H3 H4 H5 H6 H9 H10 H11 H12 H13 H14.
elim (H8 y H2); intros; elim H0; intros; elim H3; intros.
rewrite H4; rewrite H5.
clear H H0 H1 H2 H3 H4 H5 H8.
elim H7; intros; exact (H0 O H).
