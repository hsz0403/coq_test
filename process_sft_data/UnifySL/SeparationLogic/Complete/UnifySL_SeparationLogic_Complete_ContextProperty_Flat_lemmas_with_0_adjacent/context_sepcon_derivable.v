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

Lemma context_sepcon_derivable: forall (Phi Psi: context) z, context_sepcon Phi Psi |-- z -> exists x y, |-- x * y --> z /\ Phi |-- x /\ Psi |-- y.
Proof.
intros.
rewrite derivable_provable in H.
destruct H as [xs [? ?]].
revert z H0; induction H; intros.
+
exists TT, TT.
split; [| split].
-
apply aux_minimun_rule00; auto.
-
apply derivable_impp_refl.
-
apply derivable_impp_refl.
+
pose proof provable_multi_imp_arg_switch1 l x z.
pose proof modus_ponens _ _ H2 H1.
specialize (IHForall _ H3); clear H1 H2 H3.
destruct H as [x' [y' [? [? ?]]]]; subst x.
destruct IHForall as [x [y [? [? ?]]]].
exists (x && x'), (y && y').
split; [| split].
-
clear l H0 H1 H2 H3 H4.
rewrite (provable_sepcon_andp_right (x && x') y y').
rewrite (provable_sepcon_andp_left x x' y).
rewrite (provable_sepcon_andp_left x x' y').
rewrite (andp_elim1 (x * y) _).
rewrite (andp_elim2 _ (x' * y')).
rewrite <- impp_curry_uncurry.
auto.
-
apply deduction_andp_intros; auto.
-
apply deduction_andp_intros; auto.
