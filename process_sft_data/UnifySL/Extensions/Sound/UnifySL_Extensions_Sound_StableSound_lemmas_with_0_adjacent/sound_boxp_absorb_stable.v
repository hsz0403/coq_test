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

Lemma sound_boxp_absorb_stable {L: Language} {minL: MinimumLanguage L} {pL: PropositionalLanguage L} {mL: ModalLanguage L} {MD: Model} {kMD: KripkeModel MD} {M: Kmodel} {R1: KI.Relation (Kworlds M)} {R2: KM.Relation (Kworlds M)} {R3: SS.Relation (Kworlds M)} {R2_incl: Inclusion KM.Krelation SS.Krelation} {SM: Semantics L MD} {kiSM: KripkeIntuitionisticSemantics L MD M SM} {kminSM: KripkeMinimumSemantics L MD M SM} {kpSM: KripkePropositionalSemantics L MD M SM} {fmSM: FlatModalSemantics L MD M SM} {stableSM: SemanticStable L MD M SM}: forall x: expr, semantic_stable x -> (forall (m: Kworlds M), KRIPKE: M, m |= x --> boxp x).
Proof.
intros.
rewrite sat_impp.
intros.
rewrite sat_boxp.
intros.
rewrite denote_stable in H.
unfold Semantics.stable in H.
apply including in H2.
specialize (H _ _ H2).
tauto.
