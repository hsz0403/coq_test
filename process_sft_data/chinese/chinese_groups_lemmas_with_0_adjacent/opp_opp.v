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

Lemma opp_opp : is_group -> forall x : S, G x -> x = Opp (Opp x).
Proof.
intros.
apply (opp_unicity H (Opp x) x).
unfold is_opposite in |- *; split.
elim H; intros; elim H2; intros; elim H4; intros; elim (H6 x H0); intros.
elim H8; trivial.
elim H; intros; elim H2; intros; elim H4; intros; elim (H6 x H0); intros.
elim H8; intros; elim H10; auto.
