Require Import Coq.Logic.Classical_Prop.
Require Import Logic.lib.Ensembles_ext.
Require Import Logic.lib.Bijection.
Require Import Logic.lib.Countable.
Require Import Logic.GeneralLogic.Base.
Require Import Logic.GeneralLogic.KripkeModel.
Require Import Logic.GeneralLogic.ProofTheory.BasicSequentCalculus.
Require Import Logic.GeneralLogic.Semantics.Kripke.
Require Import Logic.GeneralLogic.Complete.ContextProperty.
Require Import Logic.GeneralLogic.Complete.ContextProperty_Kripke.
Require Import Logic.GeneralLogic.Complete.Lindenbaum.
Require Import Logic.GeneralLogic.Complete.Lindenbaum_Kripke.
Require Import Logic.GeneralLogic.Complete.Canonical_Kripke.
Require Import Logic.GeneralLogic.Complete.Complete_Kripke.
Require Import Logic.MinimumLogic.Syntax.
Require Import Logic.MinimumLogic.ProofTheory.Minimum.
Require Import Logic.MinimumLogic.Semantics.Kripke.
Require Import Logic.MinimumLogic.Complete.ContextProperty_Kripke.
Require Import Logic.MinimumLogic.Complete.Lindenbaum_Kripke.
Require Import Logic.MinimumLogic.Complete.Truth_Kripke.
Require Import Logic.PropositionalLogic.Syntax.
Require Import Logic.PropositionalLogic.ProofTheory.Intuitionistic.
Require Import Logic.PropositionalLogic.ProofTheory.DeMorgan.
Require Import Logic.PropositionalLogic.ProofTheory.GodelDummett.
Require Import Logic.PropositionalLogic.ProofTheory.Classical.
Require Import Logic.PropositionalLogic.Semantics.Kripke.
Require Import Logic.PropositionalLogic.Complete.ContextProperty_Kripke.
Require Import Logic.PropositionalLogic.Complete.Lindenbaum_Kripke.
Require Import Logic.PropositionalLogic.Complete.Truth_Kripke.
Require Import Logic.PropositionalLogic.Complete.Canonical_Kripke.
Require Logic.PropositionalLogic.DeepEmbedded.PropositionalLanguage.
Require Logic.PropositionalLogic.DeepEmbedded.ProofTheories.
Require Logic.PropositionalLogic.DeepEmbedded.KripkeSemantics.
Local Open Scope logic_base.
Local Open Scope syntax.
Local Open Scope kripke_model.
Local Open Scope kripke_model_class.
Import PropositionalLanguageNotation.
Import KripkeModelFamilyNotation.
Import KripkeModelNotation_Intuitionistic.
Import KripkeModelClass.
Section Complete.
Context {Sigma: PropositionalLanguage.PropositionalVariables} {CV: Countable PropositionalLanguage.Var}.
Existing Instances PropositionalLanguage.L PropositionalLanguage.minL PropositionalLanguage.pL.
Existing Instances KripkeSemantics.MD KripkeSemantics.kMD KripkeSemantics.R KripkeSemantics.SM KripkeSemantics.kminSM KripkeSemantics.kpSM.
Section General_Completeness.
Context {GammaP: Provable PropositionalLanguage.L} {GammaD: Derivable PropositionalLanguage.L}.
Definition cP : context -> Prop := Intersection _ (Intersection _ derivable_closed orp_witnessed) consistent.
Context {SC: NormalSequentCalculus _ GammaP GammaD} {bSC: BasicSequentCalculus _ GammaD} {fwSC: FiniteWitnessedSequentCalculus _ GammaD} {minSC: MinimumSequentCalculus _ GammaD} {ipSC: IntuitionisticPropositionalSequentCalculus _ GammaD} {AX: NormalAxiomatization _ GammaP GammaD} {minAX: MinimumAxiomatization _ GammaP} {ipAX: IntuitionisticPropositionalLogic _ GammaP}.
Definition canonical_frame: KripkeSemantics.frame := KripkeSemantics.Build_frame (sig cP) (fun a b => Included _ (proj1_sig a) (proj1_sig b)).
Definition canonical_eval: PropositionalLanguage.Var -> KripkeSemantics.sem canonical_frame := fun p a => proj1_sig a (PropositionalLanguage.varp p).
Definition canonical_Kmodel: @Kmodel KripkeSemantics.MD KripkeSemantics.kMD := KripkeSemantics.Build_Kmodel canonical_frame canonical_eval.
Definition rel: bijection (Kworlds canonical_Kmodel) (sig cP) := bijection_refl.
Definition H_R: forall m n Phi Psi, rel m Phi -> rel n Psi -> (m <= n <-> Included _ (proj1_sig Phi) (proj1_sig Psi)).
Proof.
intros.
change (m = Phi) in H.
change (n = Psi) in H0.
subst; reflexivity.
Existing Instances PropositionalLanguage.L PropositionalLanguage.minL PropositionalLanguage.pL.
End General_Completeness.
Section Intuitionistic_Completeness.
Existing Instances ProofTheories.IntuitionisticPropositionalLogic.GP ProofTheories.IntuitionisticPropositionalLogic.GD ProofTheories.IntuitionisticPropositionalLogic.AX ProofTheories.IntuitionisticPropositionalLogic.minAX ProofTheories.IntuitionisticPropositionalLogic.ipAX.
Existing Instances Axiomatization2SequentCalculus_SC Axiomatization2SequentCalculus_bSC Axiomatization2SequentCalculus_fwSC Axiomatization2SequentCalculus_minSC Axiomatization2SequentCalculus_ipSC.
Import Logic.PropositionalLogic.DeepEmbedded.KripkeSemantics.
End Intuitionistic_Completeness.
Section DeMorgan_Completeness.
Existing Instances ProofTheories.DeMorganPropositionalLogic.GP ProofTheories.DeMorganPropositionalLogic.GD ProofTheories.DeMorganPropositionalLogic.AX ProofTheories.DeMorganPropositionalLogic.minAX ProofTheories.DeMorganPropositionalLogic.ipAX ProofTheories.DeMorganPropositionalLogic.dmpAX.
Existing Instances Axiomatization2SequentCalculus_SC Axiomatization2SequentCalculus_bSC Axiomatization2SequentCalculus_fwSC Axiomatization2SequentCalculus_minSC Axiomatization2SequentCalculus_ipSC.
Import Logic.PropositionalLogic.DeepEmbedded.KripkeSemantics.
End DeMorgan_Completeness.
Section GodelDummett_Completeness.
Existing Instances ProofTheories.GodelDummettPropositionalLogic.GP ProofTheories.GodelDummettPropositionalLogic.GD ProofTheories.GodelDummettPropositionalLogic.AX ProofTheories.GodelDummettPropositionalLogic.minAX ProofTheories.GodelDummettPropositionalLogic.ipAX ProofTheories.GodelDummettPropositionalLogic.gdpAX.
Existing Instances Axiomatization2SequentCalculus_SC Axiomatization2SequentCalculus_bSC Axiomatization2SequentCalculus_fwSC Axiomatization2SequentCalculus_minSC Axiomatization2SequentCalculus_ipSC.
Import Logic.PropositionalLogic.DeepEmbedded.KripkeSemantics.
End GodelDummett_Completeness.
Section Classical_Completeness.
Import Logic.PropositionalLogic.DeepEmbedded.KripkeSemantics.
Existing Instances ProofTheories.ClassicalPropositionalLogic.GP ProofTheories.ClassicalPropositionalLogic.GD ProofTheories.ClassicalPropositionalLogic.AX ProofTheories.ClassicalPropositionalLogic.minAX ProofTheories.ClassicalPropositionalLogic.ipAX ProofTheories.ClassicalPropositionalLogic.cpAX.
Existing Instances Axiomatization2SequentCalculus_SC Axiomatization2SequentCalculus_bSC Axiomatization2SequentCalculus_fwSC Axiomatization2SequentCalculus_minSC Axiomatization2SequentCalculus_ipSC Axiomatization2SequentCalculus_cpSC.
End Classical_Completeness.
End Complete.

Lemma AL_OW: at_least orp_witnessed cP.
Proof.
solve_at_least.
