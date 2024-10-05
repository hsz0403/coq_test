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

Lemma add_add : commutativity S Add -> associativity S Add -> forall x1 y1 x2 y2 : S, Add (Add x1 y1) (Add x2 y2) = Add (Add x1 x2) (Add y1 y2).
Proof.
intros com ass x1 y1 x2 y2.
rewrite (ass (Add x1 y1) x2 y2); elim (ass x1 y1 x2); elim (com x2 y1).
rewrite (ass x1 x2 y1); elim (ass (Add x1 x2) y1 y2); reflexivity.
