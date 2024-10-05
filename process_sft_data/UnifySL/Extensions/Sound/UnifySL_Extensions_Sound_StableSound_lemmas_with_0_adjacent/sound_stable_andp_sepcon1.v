Require Import Coq.Sets.Ensembles.
Require Import Coq.Logic.Classical_Prop.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Equivalence.
Require Import Coq.Relations.Relation_Definitions.
Require Import Logic.lib.Ensembles_ext.
Require Import Logic.lib.Bisimulation.
Require Import Logic.GeneralLogic.Base.
Require Import Logic.GeneralLogic.KripkeModel.
Require Import Logic.ModalLogic.Model.KripkeModel.
Require Import Logic.SeparationLogic.Model.SeparationAlgebra.
Require Import Logic.MinimumLogic.Syntax.
Require Import Logic.PropositionalLogic.Syntax.
Require Import Logic.ModalLogic.Syntax.
Require Import Logic.SeparationLogic.Syntax.
Require Import Logic.Extensions.Semantics.SemanticStable.
Require Logic.PropositionalLogic.Semantics.Trivial.
Require Logic.ModalLogic.Semantics.Kripke.
Require Logic.GeneralLogic.Semantics.Kripke.
Require Logic.MinimumLogic.Semantics.Kripke.
Require Logic.PropositionalLogic.Semantics.Kripke.
Require Logic.ModalLogic.Semantics.Flat.
Require Import Logic.SeparationLogic.Semantics.WeakSemantics.
Require Logic.SeparationLogic.Semantics.FlatSemantics.
Local Open Scope logic_base.
Local Open Scope syntax.
Local Open Scope kripke_model.
Import PropositionalLanguageNotation.
Import ModalLanguageNotation.
Import SeparationLogicNotation.
Import KripkeModelFamilyNotation.
Import KripkeModelNotation_Intuitionistic.
Module Sound_Trivial.
Import Logic.PropositionalLogic.Semantics.Trivial.
Import Logic.MinimumLogic.Semantics.Trivial.
Import Logic.ModalLogic.Semantics.Kripke.
End Sound_Trivial.
Module Sound_KripkeIntuitionistic.
Import Logic.GeneralLogic.Semantics.Kripke.
Import Logic.MinimumLogic.Semantics.Kripke.
Import Logic.PropositionalLogic.Semantics.Kripke.
Import Logic.ModalLogic.Semantics.Flat.
Import Logic.SeparationLogic.Semantics.FlatSemantics.
End Sound_KripkeIntuitionistic.

Lemma sound_stable_andp_sepcon1 {L: Language} {minL: MinimumLanguage L} {pL: PropositionalLanguage L} {sepconL: SepconLanguage L} {MD: Model} {kMD: KripkeModel MD} {M: Kmodel} {R1: KI.Relation (Kworlds M)} {R2: SS.Relation (Kworlds M)} {J: Join (Kworlds M)} {SAabs: SeparationAlgebraAbsorbStable (Kworlds M)} {SM: Semantics L MD} {kiSM: KripkeIntuitionisticSemantics L MD M SM} {kminSM: KripkeMinimumSemantics L MD M SM} {kpSM: KripkePropositionalSemantics L MD M SM} {fsepconSM: SepconSemantics L MD M SM} {stableSM: SemanticStable L MD M SM}: forall x y z, semantic_stable x -> forall m: Kworlds M, KRIPKE: M, m |= (x && y) * z <--> x && (y * z).
Proof.
intros.
unfold iffp.
rewrite sat_andp, !sat_impp.
split; intros.
+
clear m H0.
rewrite sat_andp, sat_sepcon.
rewrite sat_sepcon in H1.
destruct H1 as [n1 [n2 [? [? ?]]]].
rewrite sat_andp in H1.
destruct H1.
destruct (SA_absorb_stable _ _ _ H0) as [m1 [m2 [? [? [? [? ?]]]]]].
apply (sat_mono _ _ _ H7) in H1.
apply (sat_mono _ _ _ H7) in H3.
apply (sat_mono _ _ _ H8) in H2.
rewrite denote_stable in H.
rewrite (H _ _ H5) in H1.
split; auto.
exists m1, m2; auto.
+
clear m H0.
rewrite sat_sepcon.
rewrite sat_andp, sat_sepcon in H1.
destruct H1 as [? [n1 [n2 [? [? ?]]]]].
destruct (SA_absorb_stable _ _ _ H1) as [m1 [m2 [? [? [? [? ?]]]]]].
apply (sat_mono _ _ _ H7) in H2.
apply (sat_mono _ _ _ H8) in H3.
rewrite denote_stable in H.
rewrite <- (H _ _ H5) in H0.
exists m1, m2.
split; [| split]; auto.
rewrite sat_andp.
auto.
