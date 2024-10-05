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

Lemma regular_l : is_group -> forall y z : S, G y -> G z -> forall x : S, G x -> Add x y = Add x z -> y = z.
Proof.
intros.
elim H; intros; elim H5; intros; elim H7; intros; elim H8; intros.
clear H4 H5 H7 H10.
elim (H11 y H0); intros; elim H5; clear H4 H5.
elim (H11 z H1); intros; elim H5; clear H4 H5 H8 H11.
elim (H9 x H2); intros; elim H5; intros; elim H8; intros; elim H11.
clear H4 H5 H7 H8 H9 H10 H11.
elim (H6 (Opp x) x y); elim (H6 (Opp x) x z).
elim H3; reflexivity.
