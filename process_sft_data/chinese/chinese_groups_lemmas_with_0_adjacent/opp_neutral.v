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

Lemma opp_neutral : is_group -> Opp O = O.
Proof.
intros.
elim (opp_unicity H O O).
reflexivity.
unfold is_opposite in |- *.
elim H; intros; elim H1; intros; elim H3; intros; elim H4; intros.
elim (H7 O H6); auto.
