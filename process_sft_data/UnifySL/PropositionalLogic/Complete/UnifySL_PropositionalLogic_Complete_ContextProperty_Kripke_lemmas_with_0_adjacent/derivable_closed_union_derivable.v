Require Import Coq.Logic.Classical_Prop.
Require Import Logic.lib.Coqlib.
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
Local Open Scope logic_base.
Local Open Scope syntax.
Import PropositionalLanguageNotation.
Section ContextProperties.
Context {L: Language} {minL: MinimumLanguage L} {pL: PropositionalLanguage L}.
Definition orp_witnessed: context -> Prop := fun Phi => forall x y, Phi (orp x y) -> Phi x \/ Phi y.
Context {GammaP: Provable L} {GammaD: Derivable L}.
Definition context_orp (Phi Psi: context): context := fun z => exists x y, z = x || y /\ Phi |-- x /\ Psi |-- y.
Definition context_orp_captured (P: context -> Prop): Prop := forall Phi Psi, P (context_orp Phi Psi) -> P Phi \/ P Psi.
Context {SC: NormalSequentCalculus L GammaP GammaD} {bSC: BasicSequentCalculus L GammaD} {minSC: MinimumSequentCalculus L GammaD} {ipSC: IntuitionisticPropositionalSequentCalculus L GammaD} {minAX: MinimumAxiomatization L GammaP} {ipAX: IntuitionisticPropositionalLogic L GammaP}.
End ContextProperties.

Lemma derivable_closed_union_derivable {AX: NormalAxiomatization L GammaP GammaD}: forall (Phi Psi: context) (x: expr), derivable_closed Psi -> Union _ Phi Psi |-- x -> exists y, Psi y /\ Phi |-- y --> x.
Proof.
intros.
rewrite derivable_provable in H0.
destruct H0 as [xs [? ?]].
pose proof provable_multi_imp_split _ _ _ _ H0 H1 as [xs1 [xs2 [? [? ?]]]].
pose proof H4.
rewrite <- multi_and_multi_imp in H4.
eapply modus_ponens in H4; [| apply provable_multi_imp_arg_switch1].
exists (multi_and xs2).
split.
+
apply DCS_multi_and_iff; auto.
+
rewrite derivable_provable.
exists xs1.
split; auto.
eapply modus_ponens.
-
apply provable_multi_imp_weaken.
rewrite (multi_and_multi_imp xs2 x).
apply provable_impp_refl.
-
exact H5.
