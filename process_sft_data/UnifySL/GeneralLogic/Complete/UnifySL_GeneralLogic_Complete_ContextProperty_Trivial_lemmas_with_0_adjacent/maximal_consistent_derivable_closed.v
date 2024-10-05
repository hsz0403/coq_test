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

Lemma maximal_consistent_derivable_closed: forall (Phi: context), maximal consistent Phi -> derivable_closed Phi.
Proof.
intros.
hnf; intros.
assert (consistent (Union _ Phi (Singleton _ x))).
{
destruct H as [[y ?] _].
exists y.
intro.
pose proof deduction_subst1 _ _ _ H0 H1.
auto.
}
destruct H.
specialize (H2 _ H1).
specialize (H2 (fun x H => Union_introl _ _ _ x H)).
apply H2.
right; constructor.
