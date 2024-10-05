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

Lemma DCS_andp_iff: forall (Phi: context), derivable_closed Phi -> (forall x y: expr, Phi (x && y) <-> (Phi x /\ Phi y)).
Proof.
intros.
pose proof derivable_closed_element_derivable _ H; clear H.
rewrite !H0; clear H0; split; intros.
+
pose proof deduction_andp_elim1 Phi x y H.
pose proof deduction_andp_elim2 Phi x y H.
auto.
+
destruct H.
pose proof deduction_andp_intros Phi x y H H0.
auto.
