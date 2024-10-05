Require Import Coq.Logic.Classical_Prop.
Require Import Coq.Logic.Classical_Pred_Type.
Require Import Logic.lib.Coqlib.
Require Import Logic.lib.Ensembles_ext.
Require Import Logic.lib.EnsemblesProperties.
Require Import Logic.lib.Bijection.
Require Import Logic.lib.Countable.
Require Import Logic.GeneralLogic.Base.
Require Import Logic.GeneralLogic.ProofTheory.BasicSequentCalculus.
Require Import Logic.GeneralLogic.Complete.ContextProperty.
Require Import Logic.GeneralLogic.Complete.ContextProperty_Kripke.
Require Import Logic.MinimumLogic.Syntax.
Require Import Logic.MinimumLogic.ProofTheory.Minimum.
Require Import Logic.MinimumLogic.Complete.ContextProperty_Kripke.
Require Import Logic.PropositionalLogic.Syntax.
Require Import Logic.PropositionalLogic.ProofTheory.Intuitionistic.
Require Import Logic.PropositionalLogic.ProofTheory.RewriteClass.
Require Import Logic.PropositionalLogic.ProofTheory.ProofTheoryPatterns.
Require Import Logic.PropositionalLogic.Complete.ContextProperty_Kripke.
Require Import Logic.SeparationLogic.Syntax.
Require Import Logic.SeparationLogic.ProofTheory.SeparationLogic.
Require Import Logic.SeparationLogic.ProofTheory.RewriteClass.
Require Import Logic.SeparationLogic.ProofTheory.DerivedRules.
Local Open Scope logic_base.
Local Open Scope syntax.
Import PropositionalLanguageNotation.
Import SeparationLogicNotation.
Section ContextProperties.
Context {L: Language} {minL: MinimumLanguage L} {sepconL: SepconLanguage L} {GammaP: Provable L} {GammaD: Derivable L}.
Definition context_sepcon (Phi Psi: context): context := fun z => exists x y, z = x * y /\ Phi |-- x /\ Psi |-- y.
Definition context_sepcon_included_l (Phi2 Psi: context): context -> Prop := fun Phi1 => Included _ (context_sepcon Phi1 Phi2) Psi.
Definition context_sepcon_included_r (Phi1 Psi: context): context -> Prop := fun Phi2 => Included _ (context_sepcon Phi1 Phi2) Psi.
Context {pL: PropositionalLanguage L} {wandL: WandLanguage L} {SC: NormalSequentCalculus L GammaP GammaD} {bSC: BasicSequentCalculus L GammaD} {fwSC: FiniteWitnessedSequentCalculus L GammaD} {minSC: MinimumSequentCalculus L GammaD} {ipSC: IntuitionisticPropositionalSequentCalculus L GammaD} {AX: NormalAxiomatization L GammaP GammaD} {minAX: MinimumAxiomatization L GammaP} {ipAX: IntuitionisticPropositionalLogic L GammaP} {sepconAX: SepconAxiomatization L GammaP} {wandAX: WandAxiomatization L GammaP} {sepcon_orp_AX: SepconOrAxiomatization L GammaP} {sepcon_falsep_AX: SepconFalseAxiomatization L GammaP}.
End ContextProperties.

Lemma context_sepcon_consistent_rev_left: forall (Phi1 Phi2 Psi: context), Included _ (context_sepcon Phi1 Phi2) Psi -> consistent Psi -> consistent Phi1.
Proof.
intros.
rewrite consistent_spec in H0 |- *.
intro; apply H0; clear H0.
rewrite <- (falsep_sepcon TT).
apply derivable_assum.
apply H; exists FF, TT; split; [| split]; auto.
apply derivable_impp_refl.
