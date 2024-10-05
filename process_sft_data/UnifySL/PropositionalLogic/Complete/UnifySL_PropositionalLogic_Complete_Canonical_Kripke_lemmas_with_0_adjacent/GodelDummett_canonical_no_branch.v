Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Logic.Classical_Prop.
Require Import Coq.Logic.Classical_Pred_Type.
Require Import Logic.lib.Bijection.
Require Import Logic.lib.Countable.
Require Import Logic.GeneralLogic.Base.
Require Import Logic.GeneralLogic.KripkeModel.
Require Import Logic.GeneralLogic.ProofTheory.BasicSequentCalculus.
Require Import Logic.GeneralLogic.Semantics.Kripke.
Require Import Logic.GeneralLogic.Complete.ContextProperty.
Require Import Logic.GeneralLogic.Complete.ContextProperty_Kripke.
Require Import Logic.GeneralLogic.Complete.Lindenbaum.
Require Import Logic.MinimumLogic.Syntax.
Require Import Logic.MinimumLogic.ProofTheory.Minimum.
Require Import Logic.MinimumLogic.Semantics.Kripke.
Require Import Logic.MinimumLogic.Complete.ContextProperty_Kripke.
Require Import Logic.PropositionalLogic.Syntax.
Require Import Logic.PropositionalLogic.ProofTheory.Intuitionistic.
Require Import Logic.PropositionalLogic.ProofTheory.DeMorgan.
Require Import Logic.PropositionalLogic.ProofTheory.GodelDummett.
Require Import Logic.PropositionalLogic.ProofTheory.Classical.
Require Import Logic.PropositionalLogic.Semantics.Kripke.
Require Import Logic.PropositionalLogic.Complete.ContextProperty_Kripke.
Local Open Scope logic_base.
Local Open Scope syntax.
Local Open Scope kripke_model.
Import PropositionalLanguageNotation.
Import KripkeModelFamilyNotation.
Import KripkeModelNotation_Intuitionistic.
Section Canonical.
Context {L: Language} {minL: MinimumLanguage L} {pL: PropositionalLanguage L} {Gamma: Derivable L} {bSC: BasicSequentCalculus L Gamma} {minSC: MinimumSequentCalculus L Gamma} {ipSC: IntuitionisticPropositionalSequentCalculus L Gamma} {MD: Model} {kMD: KripkeModel MD} {M: Kmodel} {R: Relation (Kworlds M)} {SM: Semantics L MD} {kminSM: KripkeMinimumSemantics L MD M SM} {kpSM: KripkePropositionalSemantics L MD M SM}.
Context (cP: context -> Prop) (rel: bijection (Kworlds M) (sig cP)).
Hypothesis H_R: forall m n Phi Psi, rel m Phi -> rel n Psi -> (m <= n <-> Included _ (proj1_sig Phi) (proj1_sig Psi)).
End Canonical.

Lemma GodelDummett_canonical_no_branch {GammaP: Provable L} {SC: NormalSequentCalculus L GammaP Gamma} {minAX: MinimumAxiomatization L GammaP} {ipAX: IntuitionisticPropositionalLogic L GammaP} {gdpAX: GodelDummettPropositionalLogic L GammaP} (AL_DC: at_least derivable_closed cP) (AL_OW: at_least orp_witnessed cP): NoBranchKripkeIntuitionisticModel (Kworlds M).
Proof.
constructor.
intros.
destruct (im_bij _ _ rel n) as [Phi ?].
destruct (im_bij _ _ rel m1) as [Psi1 ?].
destruct (im_bij _ _ rel m2) as [Psi2 ?].
erewrite !H_R in H, H0 by eauto.
do 2 erewrite H_R by eauto.
clear rel H_R m1 m2 n H1 H2 H3.
apply NNPP; intro.
apply not_or_and in H1; destruct H1.
apply not_all_ex_not in H1.
apply not_all_ex_not in H2.
destruct H1 as [x1 ?], H2 as [x2 ?].
pose proof deduction_weaken0 (proj1_sig Phi) _ (impp_choice x1 x2).
rewrite <- derivable_closed_element_derivable in H3 by (apply AL_DC, (proj2_sig Phi)).
apply AL_OW in H3; [| apply (proj2_sig Phi)].
destruct H3; pose proof H3; apply H in H3; apply H0 in H4.
+
rewrite derivable_closed_element_derivable in H3 by (apply AL_DC, (proj2_sig Psi1)).
rewrite derivable_closed_element_derivable in H4 by (apply AL_DC, (proj2_sig Psi2)).
pose proof (fun HH => deduction_modus_ponens _ _ _ HH H3).
pose proof (fun HH => deduction_modus_ponens _ _ _ HH H4).
rewrite <- !derivable_closed_element_derivable in H5 by (apply AL_DC, (proj2_sig Psi1)).
rewrite <- !derivable_closed_element_derivable in H6 by (apply AL_DC, (proj2_sig Psi2)).
clear - H1 H2 H5 H6.
tauto.
+
rewrite derivable_closed_element_derivable in H3 by (apply AL_DC, (proj2_sig Psi1)).
rewrite derivable_closed_element_derivable in H4 by (apply AL_DC, (proj2_sig Psi2)).
pose proof (fun HH => deduction_modus_ponens _ _ _ HH H3).
pose proof (fun HH => deduction_modus_ponens _ _ _ HH H4).
rewrite <- !derivable_closed_element_derivable in H5 by (apply AL_DC, (proj2_sig Psi1)).
rewrite <- !derivable_closed_element_derivable in H6 by (apply AL_DC, (proj2_sig Psi2)).
clear - H1 H2 H5 H6.
tauto.
