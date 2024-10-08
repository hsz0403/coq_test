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
Admitted.

Lemma add_add : commutativity S Add -> associativity S Add -> forall x1 y1 x2 y2 : S, Add (Add x1 y1) (Add x2 y2) = Add (Add x1 x2) (Add y1 y2).
Proof.
intros com ass x1 y1 x2 y2.
rewrite (ass (Add x1 y1) x2 y2); elim (ass x1 y1 x2); elim (com x2 y1).
Admitted.

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
Admitted.

Lemma opp_opp : is_group -> forall x : S, G x -> x = Opp (Opp x).
Proof.
intros.
apply (opp_unicity H (Opp x) x).
unfold is_opposite in |- *; split.
elim H; intros; elim H2; intros; elim H4; intros; elim (H6 x H0); intros.
elim H8; trivial.
elim H; intros; elim H2; intros; elim H4; intros; elim (H6 x H0); intros.
Admitted.

Lemma opp_neutral : is_group -> Opp O = O.
Proof.
intros.
elim (opp_unicity H O O).
reflexivity.
unfold is_opposite in |- *.
elim H; intros; elim H1; intros; elim H3; intros; elim H4; intros.
Admitted.

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
