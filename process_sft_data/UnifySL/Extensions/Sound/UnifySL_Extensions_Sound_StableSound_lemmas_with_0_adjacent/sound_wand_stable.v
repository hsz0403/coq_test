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

Lemma sound_wand_stable {L: Language} {minL: MinimumLanguage L} {pL: PropositionalLanguage L} {wandL: WandLanguage L} {MD: Model} {kMD: KripkeModel MD} {M: Kmodel} {R1: KI.Relation (Kworlds M)} {R2: SS.Relation (Kworlds M)} {J: Join (Kworlds M)} {SAbis: SeparationAlgebraBisStable (Kworlds M)} {SM: Semantics L MD} {fwandSM: WandSemantics L MD M SM} {stableSM: SemanticStable L MD M SM}: forall x y: expr, semantic_stable x -> semantic_stable y -> semantic_stable (x -* y).
Proof.
intros.
rewrite denote_stable in H, H0 |- *.
unfold Semantics.stable in *.
intros.
rewrite !(app_same_set (denote_wand _ _)).
unfold WeakSemantics.wand; simpl.
pose proof extend_bis_stable _ _ H1.
split.
+
intros ? n1 n2 ? ?.
destruct H2 as [_ ?].
specialize (H2 _ _ H4).
destruct H2 as [m1 [m2 [? [? ?]]]].
specialize (H3 _ _ H2).
specialize (H0 _ _ H7).
specialize (H _ _ H6).
tauto.
+
intros ? m1 m2 ? ?.
destruct H2 as [? _].
specialize (H2 _ _ H4).
destruct H2 as [n1 [n2 [? [? ?]]]].
specialize (H3 _ _ H2).
specialize (H0 _ _ H7).
specialize (H _ _ H6).
tauto.
