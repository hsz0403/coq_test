Require Export Classical.
Require Import ClassicalChoice.
Require Export Relation_Definitions.
Require Import Relation_Definitions_Implicit.
Require Export Ensembles.
Require Import EnsemblesImplicit.
Require Import ProofIrrelevance.
Require Import InverseImage.
Require Export EnsemblesSpec.
Require Import Quotients.
Section ZL'.
Variable T:Type.
Variable R:relation T.
Hypothesis ord:order R.
Definition chain (S: Ensemble T) : Prop := forall x y:T, In S x -> In S y -> (R x y \/ R y x).
Definition maximal (x:T) : Prop := forall y:T, R x y -> x = y.
Variable chain_sup: forall S: Ensemble T, chain S -> { x:T | (forall y:T, In S y -> R y x) /\ (forall z:T, (forall y:T, In S y -> R y z) -> R x z) }.
Variable inflation: forall x:T, { y:T | R x y /\ x <> y /\ forall z:T, R x z -> R z y -> z = x \/ z = y }.
Inductive tower : Ensemble T := | sup_intro: forall (S: Ensemble T), Included S tower -> forall c:chain S, In tower (proj1_sig (chain_sup S c)) | inflation_intro: forall x:T, In tower x -> In tower (proj1_sig (inflation x)).
End ZL'.
Arguments chain {T}.
Arguments maximal {T}.
Require Export EnsemblesSpec.
Section ZL.
Variable T:Type.
Variable R:relation T.
Hypothesis ord: order R.
Hypothesis ub_of_chain: forall S:Ensemble T, chain R S -> exists x:T, forall y:T, In S y -> R y x.
Definition chains := {S:Ensemble T | chain R S}.
Definition chains_ord := (fun S1 S2:chains => Included (proj1_sig S1) (proj1_sig S2)).
Definition chains_sup_def : forall F: Ensemble chains, chain chains_ord F -> chains.
refine (fun F H => exist _ [ x:T | exists S:chains, In F S /\ In (proj1_sig S) x ] _).
red; intros.
destruct H0, H1, H0, H1.
pose proof (H x0 x1).
destruct x0, x1, H0, H1.
apply H2 in H0; trivial.
destruct H0; apply c0 + apply c; trivial; now apply H0.
Defined.
Definition chains_sup (F:Ensemble chains) (P:chain chains_ord F) := let U := chains_sup_def F P in exist (fun U:chains => (forall S:chains, In F S -> chains_ord S U) /\ (forall T:chains, (forall S:chains, In F S -> chains_ord S T) -> chains_ord U T)) (chains_sup_def F P) (chains_sup_correct F P).
End ZL.
Arguments ZornsLemma {T}.
Section ZL_preorder.
Variable T:Type.
Variable R:relation T.
Hypothesis Rpreord: preorder R.
Hypothesis ub_of_chain: forall S:Ensemble T, chain R S -> exists x:T, forall y:T, In S y -> R y x.
Definition premaximal (x:T) : Prop := forall y:T, R x y -> R y x.
Local Definition Requiv (x y:T) := R x y /\ R y x.
Local Lemma equivalence_Requiv : equivalence Requiv.
Proof.
constructor.
-
intro.
split; now apply preord_refl.
-
intros x y z [H0 H1] [H2 H3].
split; now apply preord_trans with y.
-
intros x y [H1 H2].
now split.
End ZL_preorder.
Arguments premaximal {T}.

Lemma tower_is_chain: chain tower.
Proof.
unfold chain.
intros.
revert x H.
induction H0.
-
intros.
case (classic (forall y:T, In S y -> R y x)).
+
right.
now apply (proj2_sig (chain_sup S c)).
+
intro.
left.
apply not_all_ex_not in H2.
destruct H2.
apply imply_to_and in H2.
destruct H2.
apply (ord_trans ord) with x0.
*
pose proof (H0 x0 H2 x H1).
tauto.
*
now apply (proj2_sig (chain_sup S c)).
-
pose proof (proj2_sig (inflation x)).
destruct H0, H1.
remember (proj1_sig (inflation x)) as x'.
assert (forall y:T, In tower y -> R y x \/ R x' y).
+
intros.
induction H3.
*
case (classic (forall x0:T, In S x0 -> R x0 x)); trivial.
left.
now apply (proj2_sig (chain_sup S c)).
right.
apply not_all_ex_not in H5.
destruct H5.
apply imply_to_and in H5.
destruct H5.
apply (ord_trans ord) with x0.
**
pose proof (H4 x0).
tauto.
**
now apply (proj2_sig (chain_sup S c)).
*
assert (In tower x').
rewrite Heqx'.
now apply inflation_intro.
destruct IHtower0.
**
assert (In tower (proj1_sig (inflation x0))) by now apply inflation_intro.
case (IHtower (proj1_sig (inflation x0)) H6); [ now left | ].
intro.
pose proof (proj2_sig (inflation x0)).
simpl in H8.
assert (x = x0 \/ x = proj1_sig (inflation x0)) by now apply H8.
case H9.
***
right.
rewrite Heqx', H10.
apply (ord_refl ord).
***
left.
rewrite H10.
apply (ord_refl ord).
**
right.
now apply (ord_trans ord) with x0, (proj2_sig (inflation x0)).
+
intros.
case (H3 x0 H4).
*
left.
now apply (ord_trans ord) with x.
*
now right.
