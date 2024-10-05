Require Import Coq.Logic.Classical_Prop.
Require Import Logic.lib.Coqlib.
Require Import Logic.GeneralLogic.Base.
Require Import Logic.GeneralLogic.Complete.ContextProperty.
Require Import Logic.GeneralLogic.ProofTheory.BasicSequentCalculus.
Require Import Logic.GeneralLogic.Complete.ContextProperty_Kripke.
Local Open Scope logic_base.
Section ContextProperty.
Context {L: Language} {Gamma: Derivable L} {bSC: BasicSequentCalculus L Gamma}.
End ContextProperty.

Lemma maximal_consistent_spec : forall Phi, maximal consistent Phi <-> consistent Phi /\ forall x, consistent (Union _ Phi (Singleton _ x)) -> Phi x.
Proof.
intros.
split; intros [? ?]; split; auto.
+
intros.
specialize (H0 _ H1).
specialize (H0 (fun x H => Union_introl _ _ _ _ H)).
specialize (H0 x).
apply H0; right; constructor.
+
intros.
hnf; intros.
apply H0.
unfold consistent in*.
destruct H1 as [y ?].
exists y.
intro; apply H1.
eapply deduction_weaken; [| exact H4].
intros ? [? | ?]; auto.
destruct H5; auto.
