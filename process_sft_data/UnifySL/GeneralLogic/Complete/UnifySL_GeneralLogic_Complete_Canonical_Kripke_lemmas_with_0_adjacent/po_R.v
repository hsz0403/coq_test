Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Logic.Classical_Prop.
Require Import Coq.Logic.Classical_Pred_Type.
Require Import Logic.lib.Bijection.
Require Import Logic.lib.Countable.
Require Import Logic.GeneralLogic.Base.
Require Import Logic.GeneralLogic.KripkeModel.
Require Import Logic.GeneralLogic.ProofTheory.BasicSequentCalculus.
Require Import Logic.GeneralLogic.Semantics.Kripke.
Require Import Logic.GeneralLogic.Complete.ContextProperty_Kripke.
Local Open Scope logic_base.
Local Open Scope kripke_model.
Import KripkeModelFamilyNotation.
Import KripkeModelNotation_Intuitionistic.
Section Canonical.
Context {L: Language} {Gamma: Derivable L} {bSC: BasicSequentCalculus L Gamma} {MD: Model} {kMD: KripkeModel MD} {M: Kmodel} {R: Relation (Kworlds M)} {SM: Semantics L MD}.
Context (cP: context -> Prop) (rel: bijection (Kworlds M) (sig cP)).
Hypothesis H_R: forall m n Phi Psi, rel m Phi -> rel n Psi -> (m <= n <-> Included _ (proj1_sig Phi) (proj1_sig Psi)).
Instance po_R: PreOrder (@KI.Krelation _ R).
Proof.
constructor.
+
hnf; intros m.
destruct (im_bij _ _ rel m) as [Phi ?].
apply (H_R _ _ _ _ H H).
hnf; intros; auto.
+
hnf; intros m1 m2 m3.
destruct (im_bij _ _ rel m1) as [Phi1 ?].
destruct (im_bij _ _ rel m2) as [Phi2 ?].
destruct (im_bij _ _ rel m3) as [Phi3 ?].
rewrite (H_R _ _ _ _ H H0).
rewrite (H_R _ _ _ _ H0 H1).
rewrite (H_R _ _ _ _ H H1).
clear; unfold Included, Ensembles.In; firstorder.
End Canonical.

Instance po_R: PreOrder (@KI.Krelation _ R).
Proof.
constructor.
+
hnf; intros m.
destruct (im_bij _ _ rel m) as [Phi ?].
apply (H_R _ _ _ _ H H).
hnf; intros; auto.
+
hnf; intros m1 m2 m3.
destruct (im_bij _ _ rel m1) as [Phi1 ?].
destruct (im_bij _ _ rel m2) as [Phi2 ?].
destruct (im_bij _ _ rel m3) as [Phi3 ?].
rewrite (H_R _ _ _ _ H H0).
rewrite (H_R _ _ _ _ H0 H1).
rewrite (H_R _ _ _ _ H H1).
clear; unfold Included, Ensembles.In; firstorder.
