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

Lemma classical_canonical_ident {cpSC: ClassicalPropositionalSequentCalculus L Gamma} (AL_DC: at_least derivable_closed cP) (AL_OW: at_least orp_witnessed cP) (AL_CONSI: at_least consistent cP): IdentityKripkeIntuitionisticModel (Kworlds M).
Proof.
constructor.
intros.
destruct (im_bij _ _ rel m) as [Phi ?].
destruct (im_bij _ _ rel n) as [Psi ?].
erewrite H_R in H by eauto.
assert (Phi = Psi); [| subst; eapply (in_bij _ _ rel); eauto].
clear rel H_R m n H0 H1.
apply sig_context_ext.
intros; split; [apply H; auto |].
intros.
pose proof derivable_excluded_middle (proj1_sig Phi) x.
rewrite <- derivable_closed_element_derivable in H1 by (apply AL_DC, (proj2_sig Phi)).
apply AL_OW in H1; [| apply (proj2_sig Phi)].
destruct H1; auto.
exfalso.
apply H in H1; unfold Ensembles.In in H1.
rewrite derivable_closed_element_derivable in H0, H1 by (apply AL_DC, (proj2_sig Psi)).
pose proof deduction_modus_ponens _ _ _ H0 H1.
revert H2; change (~ proj1_sig Psi |-- FF).
rewrite <- consistent_spec.
apply AL_CONSI, (proj2_sig Psi).
