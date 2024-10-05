Require Import Coq.Logic.Classical_Prop.
Require Import Logic.lib.Ensembles_ext.
Require Import Logic.GeneralLogic.Base.
Require Import Logic.GeneralLogic.KripkeModel.
Require Import Logic.MinimumLogic.Syntax.
Require Logic.MinimumLogic.Sound.Sound_Classical_Trivial.
Require Logic.MinimumLogic.Sound.Sound_Kripke.
Require Import Logic.PropositionalLogic.Syntax.
Require Import Logic.PropositionalLogic.Semantics.Trivial.
Require Import Logic.PropositionalLogic.Semantics.Kripke.
Require Logic.PropositionalLogic.Sound.Sound_Classical_Trivial.
Require Logic.PropositionalLogic.Sound.Sound_Kripke.
Require Logic.PropositionalLogic.DeepEmbedded.PropositionalLanguage.
Require Logic.PropositionalLogic.DeepEmbedded.ProofTheories.
Require Logic.PropositionalLogic.DeepEmbedded.TrivialSemantics.
Require Logic.PropositionalLogic.DeepEmbedded.KripkeSemantics.
Local Open Scope logic_base.
Local Open Scope syntax.
Local Open Scope kripke_model.
Local Open Scope kripke_model_class.
Import PropositionalLanguageNotation.
Import KripkeModelFamilyNotation.
Import KripkeModelNotation_Intuitionistic.
Import KripkeModelClass.
Section Sound.
Context {Sigma: PropositionalLanguage.PropositionalVariables}.
Existing Instances PropositionalLanguage.L PropositionalLanguage.minL PropositionalLanguage.pL.
Section Sound_Classical_Trivial.
Import Logic.MinimumLogic.Semantics.Trivial.
Import Logic.MinimumLogic.Sound.Sound_Classical_Trivial.
Import Logic.PropositionalLogic.Sound.Sound_Classical_Trivial.
Existing Instances ProofTheories.ClassicalPropositionalLogic.minAX ProofTheories.ClassicalPropositionalLogic.ipAX.
Existing Instances TrivialSemantics.MD TrivialSemantics.SM TrivialSemantics.tminSM TrivialSemantics.tpSM.
End Sound_Classical_Trivial.
Section Sound_Kripke.
Import Logic.MinimumLogic.Sound.Sound_Kripke.
Import Logic.PropositionalLogic.Sound.Sound_Kripke.
Import Logic.PropositionalLogic.DeepEmbedded.KripkeSemantics.
Existing Instances ProofTheories.IntuitionisticPropositionalLogic.minAX ProofTheories.IntuitionisticPropositionalLogic.ipAX.
Existing Instances KripkeSemantics.MD KripkeSemantics.kMD KripkeSemantics.SM KripkeSemantics.kminSM KripkeSemantics.kpSM KripkeSemantics.R.
End Sound_Kripke.
End Sound.

Theorem sound_GodelDummett_Kripke_no_branch: provable_sound ProofTheories.GodelDummettPropositionalLogic.GP KripkeSemantics.SM (KripkeModelClass _ (Kmodel_Monotonic + Kmodel_PreOrder + Kmodel_NoBranch)).
Proof.
hnf; intros.
intros _ [M m [[mono po_R] nkiM]].
pose proof (@KripkeSemantics.kiSM Sigma M mono po_R) as kiSM.
hnf in mono, po_R, nkiM.
induction H.
+
pose proof sound_modus_ponens x y m.
exact (H1 IHprovable1 IHprovable2).
+
apply sound_axiom1.
+
apply sound_axiom2.
+
apply sound_andp_intros.
+
apply sound_andp_elim1.
+
apply sound_andp_elim2.
+
apply sound_orp_intros1.
+
apply sound_orp_intros2.
+
apply sound_orp_elim.
+
apply sound_falsep_elim.
+
apply sound_impp_choice_no_branch.
