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

Lemma sound_boxp_stable {L: Language} {minL: MinimumLanguage L} {pL: PropositionalLanguage L} {mL: ModalLanguage L} {MD: Model} {kMD: KripkeModel MD} {M: Kmodel} {R1: KI.Relation (Kworlds M)} {R2: KM.Relation (Kworlds M)} {R3: SS.Relation (Kworlds M)} {R2_bis: Bisimulation SS.Krelation KM.Krelation} {SM: Semantics L MD} {fmSM: FlatModalSemantics L MD M SM} {stableSM: SemanticStable L MD M SM}: forall x: expr, semantic_stable x -> semantic_stable (boxp x).
Proof.
intros.
rewrite denote_stable in H |- *.
unfold Semantics.stable in *.
intros.
rewrite !(app_same_set (denote_boxp _)).
unfold Semantics.boxp; simpl.
split.
+
pose proof bis_r _ _ H0.
intros.
specialize (H1 _ H3).
destruct H1 as [m0 [? ?]].
specialize (H2 _ H1).
specialize (H _ _ H4).
tauto.
+
pose proof bis_l _ _ H0.
intros.
rename n0 into m0.
specialize (H1 _ H3).
destruct H1 as [n0 [? ?]].
specialize (H2 _ H1).
specialize (H _ _ H4).
tauto.
