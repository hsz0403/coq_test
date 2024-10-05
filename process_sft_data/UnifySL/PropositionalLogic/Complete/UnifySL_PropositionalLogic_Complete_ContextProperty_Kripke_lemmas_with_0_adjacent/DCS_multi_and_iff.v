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

Lemma DCS_multi_and_iff: forall (Phi: context), derivable_closed Phi -> (forall xs: list expr, Phi (multi_and xs) <-> Forall Phi xs).
Proof.
intros.
rewrite (DCS_iffp Phi (multi_and xs) (fold_right andp TT xs)).
2: auto.
2: apply multi_and_spec.
induction xs.
+
split; intros.
-
constructor.
-
simpl.
apply DCS_truep; auto.
+
simpl.
rewrite DCS_andp_iff by auto.
rewrite IHxs.
clear.
split; intros.
-
constructor; tauto.
-
inversion H; auto.
