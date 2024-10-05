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

Lemma context_sepcon_included_l_context_orp_captured: forall Phi2 Psi (DC: derivable_closed Psi) (OW: orp_witnessed Psi), context_orp_captured (context_sepcon_included_l Phi2 Psi).
Proof.
intros.
unfold context_sepcon_included_l.
hnf; intros Phi1 Phi1' ?.
assert (forall z1 z2, context_sepcon Phi1 Phi2 z1 -> ~ Psi z1 -> context_sepcon Phi1' Phi2 z2 -> ~ Psi z2 -> False) as HH.
2: {
clear - HH; unfold Included, Ensembles.In.
apply NNPP; intro.
apply not_or_and in H; destruct H.
apply not_all_ex_not in H.
apply not_all_ex_not in H0.
destruct H as [z1 ?], H0 as [z2 ?].
specialize (HH z1 z2).
tauto.
}
intros.
destruct H0 as [x1 [y1 [? [? ?]]]], H2 as [x2 [y2 [? [? ?]]]].
subst z1 z2.
assert (context_orp Phi1 Phi1' (x1 || x2)); [| assert (context_sepcon (context_orp Phi1 Phi1') Phi2 ((x1 || x2) * (y1 && y2))); [| assert (Psi |-- (x1 * y1) || (x2 * y2))]].
+
exists x1, x2.
split; [| split]; auto.
+
exists (x1 || x2), (y1 && y2).
split; [| split]; auto.
-
apply derivable_assum; auto.
-
apply deduction_andp_intros; auto.
+
apply H in H2.
apply derivable_assum in H2.
rewrite sepcon_orp_distr_r in H2.
rewrite (andp_elim1 y1 y2) in H2 at 1.
rewrite (andp_elim2 y1 y2) in H2 at 1.
auto.
+
rewrite <- derivable_closed_element_derivable in H8 by auto.
apply OW in H8.
tauto.
