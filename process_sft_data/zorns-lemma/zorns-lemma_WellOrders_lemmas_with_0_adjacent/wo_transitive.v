Require Export Relation_Definitions.
Require Import Relation_Definitions_Implicit.
Require Import Classical_Wf.
Require Import Description.
Require Import FunctionalExtensionality.
Require Import Classical.
Require Import ZornsLemma.
Require Import ProofIrrelevance.
Require Import EnsemblesSpec.
Section WellOrder.
Variable T:Type.
Definition total_strict_order (R:relation T) : Prop := forall x y:T, R x y \/ x = y \/ R y x.
Record well_order (R:relation T) : Prop := { wo_well_founded: well_founded R; wo_total_strict_order: total_strict_order R }.
End WellOrder.
Arguments total_strict_order {T}.
Arguments well_order {T}.
Arguments wo_well_founded {T} {R}.
Arguments wo_transitive {T} {R}.
Arguments wo_total_strict_order {T} {R}.
Arguments wo_irrefl {T} {R}.
Arguments wo_antisym {T} {R}.
Section WellOrderMinimum.
Variable T:Type.
Variable R:relation T.
Hypothesis well_ord: well_order R.
Definition WO_minimum: forall S:Ensemble T, Inhabited S -> { x:T | In S x /\ forall y:T, In S y -> y = x \/ R x y }.
refine (fun S H => constructive_definite_description _ _).
pose proof (WF_implies_MEP T R (wo_well_founded well_ord)).
unfold minimal_element_property in H0.
pose proof (H0 S H).
destruct H1.
destruct H1.
exists x.
red.
split.
split.
assumption.
intros.
case (wo_total_strict_order well_ord x y).
tauto.
intro.
case H4.
auto.
intro.
contradict H5.
auto.
intros.
destruct H3.
case (wo_total_strict_order well_ord x x').
intro.
pose proof (H4 x H1).
case H6.
trivial.
intro.
contradict H7.
auto.
intro.
case H5.
trivial.
intro.
contradict H6.
auto.
Defined.
End WellOrderMinimum.
Arguments WO_minimum {T}.
Section WellOrderConstruction.
Variable T:Type.
Definition restriction_relation (R:relation T) (S:Ensemble T) : relation ({z:T | In S z}) := fun (x y:{z:T | In S z}) => R (proj1_sig x) (proj1_sig y).
Record partial_WO : Type := { pwo_S: Ensemble T; pwo_R: relation T; pwo_R_lives_on_S: forall (x y:T), pwo_R x y -> In pwo_S x /\ In pwo_S y; pwo_wo: well_order (restriction_relation pwo_R pwo_S) }.
Record partial_WO_ord (WO1 WO2:partial_WO) : Prop := { pwo_S_incl: Included (pwo_S WO1) (pwo_S WO2); pwo_restriction: forall x y:T, In (pwo_S WO1) x -> In (pwo_S WO1) y -> (pwo_R WO1 x y <-> pwo_R WO2 x y); pwo_downward_closed: forall x y:T, In (pwo_S WO1) y -> In (pwo_S WO2) x -> pwo_R WO2 x y -> In (pwo_S WO1) x }.
Definition partial_WO_chain_ub: forall C:Ensemble partial_WO, chain partial_WO_ord C -> partial_WO.
refine (fun C H => let US := [ x:T | exists WO:partial_WO, In C WO /\ In (pwo_S WO) x ] in let UR := fun x y:T => exists WO:partial_WO, In C WO /\ pwo_R WO x y in Build_partial_WO US UR _ _).
intros.
unfold UR in H0.
destruct H0.
destruct H0.
split.
constructor.
exists x0.
split.
assumption.
pose proof (pwo_R_lives_on_S x0 x y).
tauto.
constructor.
exists x0.
split.
assumption.
pose proof (pwo_R_lives_on_S x0 x y).
tauto.
constructor.
assert (forall (WO:partial_WO) (x:{z:T | In (pwo_S WO) z}), In C WO -> In US (proj1_sig x)).
intros.
constructor.
exists WO.
split.
assumption.
exact (proj2_sig x).
assert (forall (WO:partial_WO) (iC:In C WO) (x:{z:T | In (pwo_S WO) z}), Acc (restriction_relation (pwo_R WO) (pwo_S WO)) x -> Acc (restriction_relation UR US) (exist _ (proj1_sig x) (H0 WO x iC))).
intros.
induction H1.
constructor.
intros.
destruct x as [x ix].
destruct y as [y iy].
unfold restriction_relation in H3.
simpl in H3.
assert (In (pwo_S WO) y).
destruct H3.
destruct H3.
pose proof (H WO x0 iC H3).
case H5.
intro.
destruct H6.
apply pwo_downward_closed0 with x.
assumption.
pose proof (pwo_R_lives_on_S x0 y x).
tauto.
assumption.
intro.
destruct H6.
apply pwo_S_incl0.
pose proof (pwo_R_lives_on_S x0 y x).
tauto.
pose proof (H2 (exist (In (pwo_S WO)) y H4)).
simpl in H5.
assert (iy = H0 WO (exist (In (pwo_S WO)) y H4) iC).
apply proof_irrelevance.
rewrite <- H6 in H5.
apply H5.
unfold restriction_relation.
simpl.
destruct H3.
destruct H3.
pose proof (H WO x0 iC H3).
case H8.
intros.
destruct H9.
apply <- pwo_restriction0.
assumption.
assumption.
assumption.
intro.
destruct H9.
apply -> pwo_restriction0.
assumption.
pose proof (pwo_R_lives_on_S x0 y x).
tauto.
pose proof (pwo_R_lives_on_S x0 y x).
tauto.
red.
intro.
destruct a.
inversion i.
destruct H2.
destruct H2.
pose proof (H1 x0 H2 (exist _ x H3)).
simpl in H4.
assert (i = H0 x0 (exist _ x H3) H2).
apply proof_irrelevance.
rewrite <- H5 in H4.
apply H4.
apply (wo_well_founded (pwo_wo x0)).
unfold total_strict_order.
intros.
destruct x.
destruct y.
unfold restriction_relation.
simpl.
destruct i.
destruct e.
destruct a.
destruct i0.
destruct e.
destruct a.
case (H x1 x2 i i0).
intro.
assert (In (pwo_S x2) x).
apply H0.
assumption.
case (wo_total_strict_order (pwo_wo x2) (exist _ x H1) (exist _ x0 i2)).
unfold restriction_relation.
simpl.
left.
exists x2.
tauto.
intro.
case H2.
right; left.
apply subset_eq_compat.
injection H3.
trivial.
unfold restriction_relation.
simpl.
right; right.
exists x2.
tauto.
intro.
assert (In (pwo_S x1) x0).
apply H0.
assumption.
case (wo_total_strict_order (pwo_wo x1) (exist _ x i1) (exist _ x0 H1)).
unfold restriction_relation.
simpl.
left.
exists x1.
tauto.
intro.
case H2.
right; left.
apply subset_eq_compat.
injection H3.
trivial.
unfold restriction_relation; simpl.
right; right.
exists x1.
tauto.
Defined.
Definition extend_strictly_partial_WO: forall (WO:partial_WO) (a:T), ~ In (pwo_S WO) a -> partial_WO.
refine (fun WO a H => let S' := Add (pwo_S WO) a in let R' := fun x y:T => pwo_R WO x y \/ (In (pwo_S WO) x /\ y = a) in Build_partial_WO S' R' _ _).
intros.
case H0.
intros.
split.
left.
pose proof (pwo_R_lives_on_S WO x y).
tauto.
left.
pose proof (pwo_R_lives_on_S WO x y).
tauto.
intros.
destruct H1.
split.
left.
assumption.
right.
rewrite H2.
auto with sets.
constructor.
red.
intros.
assert (forall x:{y:T | In (pwo_S WO) y}, In S' (proj1_sig x)).
intro.
destruct x.
left.
simpl.
assumption.
assert (forall x:{y:T | In (pwo_S WO) y}, Acc (restriction_relation R' S') (exist _ (proj1_sig x) (H0 x))).
intro.
pose proof (wo_well_founded (pwo_wo WO) x).
induction H1.
constructor.
intros.
destruct x.
destruct y.
unfold restriction_relation in H3.
simpl in H3.
assert (In (pwo_S WO) x0).
case H3.
intro.
pose proof (pwo_R_lives_on_S WO x0 x).
tauto.
tauto.
assert (pwo_R WO x0 x).
case H3.
trivial.
intro.
destruct H5.
contradict H.
rewrite <- H6.
assumption.
pose proof (H2 (exist _ x0 H4)).
simpl in H6.
assert (i0 = (H0 (exist (In (pwo_S WO)) x0 H4))).
apply proof_irrelevance.
rewrite <- H7 in H6.
apply H6.
red.
simpl.
assumption.
destruct a0.
case i.
intros.
pose proof (H1 (exist _ x0 i0)).
simpl in H2.
assert (H0 (exist (In (pwo_S WO)) x0 i0) = Union_introl T (pwo_S WO) (Singleton a) x0 i0).
apply proof_irrelevance.
rewrite <- H3.
assumption.
intros.
generalize i0.
destruct i0.
intro.
constructor.
intros.
unfold restriction_relation in H2.
destruct y.
simpl in H2.
case H2.
intro.
contradict H.
pose proof (pwo_R_lives_on_S WO x0 a).
tauto.
intros.
destruct H3.
pose proof (H1 (exist _ x0 H3)).
simpl in H5.
assert (H0 (exist (In (pwo_S WO)) x0 H3) = i1).
apply proof_irrelevance.
rewrite H6 in H5.
assumption.
red.
intros.
destruct x.
destruct y.
unfold restriction_relation.
simpl.
case i.
case i0.
intros.
case (wo_total_strict_order (pwo_wo WO) (exist _ x2 i2) (exist _ x1 i1)).
intro.
red in H0.
simpl in H0.
left.
constructor 1.
assumption.
intro.
case H0.
right; left.
apply subset_eq_compat.
injection H1.
trivial.
right; right.
red in H1.
simpl in H1.
constructor 1.
assumption.
intros.
left.
destruct i1.
constructor 2.
tauto.
case i0.
intros.
right; right.
destruct i2.
constructor 2.
tauto.
right; left.
apply subset_eq_compat.
destruct i1.
destruct i2.
trivial.
Defined.
End WellOrderConstruction.
Section WO_implies_AC.
End WO_implies_AC.

Lemma wo_transitive: forall R:relation T, well_order R -> transitive R.
Proof.
intros.
unfold transitive.
intros.
case (wo_total_strict_order R H x z).
trivial.
intro.
case H2.
intro.
rewrite H3 in H0.
pose proof (wo_antisym R H y z).
contradict H0.
auto.
intro.
assert (forall a:T, Acc R a -> a <> x /\ a <> y /\ a <> z).
intros.
induction H4.
intuition.
rewrite H2 in H5.
pose proof (H5 z H3).
tauto.
rewrite H2 in H5.
pose proof (H5 x H0).
tauto.
rewrite H2 in H5.
pose proof (H5 y H1).
tauto.
rewrite H2 in H5.
pose proof (H5 z H3).
tauto.
rewrite H2 in H5.
pose proof (H5 x H0).
tauto.
rewrite H2 in H5.
pose proof (H5 y H1).
tauto.
pose proof (wo_well_founded R H).
unfold well_founded in H5.
pose proof (H4 x (H5 x)).
tauto.
