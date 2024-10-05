Require Import Logic.lib.Coqlib.
Require Import Logic.GeneralLogic.Base.
Require Import Logic.GeneralLogic.KripkeModel.
Require Import Logic.GeneralLogic.Semantics.Kripke.
Require Import Logic.MinimumLogic.Syntax.
Require Import Logic.MinimumLogic.Semantics.Kripke.
Require Import Logic.PropositionalLogic.Syntax.
Require Import Logic.PropositionalLogic.Semantics.Kripke.
Require Import Logic.SeparationLogic.Syntax.
Require Import Logic.SeparationLogic.Model.SeparationAlgebra.
Require Import Logic.SeparationLogic.Model.OrderedSA.
Require Import Logic.SeparationLogic.Semantics.DownwardsSemantics.
Local Open Scope logic_base.
Local Open Scope syntax.
Local Open Scope kripke_model.
Import PropositionalLanguageNotation.
Import SeparationLogicNotation.
Import KripkeModelFamilyNotation.
Import KripkeModelNotation_Intuitionistic.
Section Sound_Downwards.
Context {L: Language} {minL: MinimumLanguage L} {pL: PropositionalLanguage L} {sepconL: SepconLanguage L} {wandL: WandLanguage L} {MD: Model} {kMD: KripkeModel MD} (M: Kmodel) {R: Relation (Kworlds M)} {po_R: PreOrder Krelation} {J: Join (Kworlds M)} {SA: SeparationAlgebra (Kworlds M)} {dSA: DownwardsClosedSeparationAlgebra (Kworlds M)} {SM: Semantics L MD} {kiSM: KripkeIntuitionisticSemantics L MD M SM} {kminSM: KripkeMinimumSemantics L MD M SM} {kpSM: KripkePropositionalSemantics L MD M SM} {dsepconSM: DownwardsSemantics.SepconSemantics L MD M SM} {dwandSM: DownwardsSemantics.WandSemantics L MD M SM}.
Context {empL: EmpLanguage L} {dempSM: DownwardsSemantics.EmpSemantics L MD M SM}.
End Sound_Downwards.

Lemma sound_sepcon_mono: forall x1 x2 y1 y2: expr, (forall m, KRIPKE: M, m |= x1 --> x2) -> (forall m, KRIPKE: M, m |= y1 --> y2) -> (forall m, KRIPKE: M, m |= x1 * y1 --> x2 * y2).
Proof.
intros.
assert (ASSUx: forall m, KRIPKE: M, m |= x1 -> KRIPKE: M, m |= x2).
{
intros.
specialize (H m0).
rewrite sat_impp in H.
apply (H m0); [reflexivity | auto].
}
assert (ASSUy: forall m, KRIPKE: M, m |= y1 -> KRIPKE: M, m |= y2).
{
intros.
specialize (H0 m0).
rewrite sat_impp in H0.
apply (H0 m0); [reflexivity | auto].
}
rewrite sat_impp; intros.
rewrite sat_sepcon in H2 |- *.
destruct H2 as [m0 [m1 [m2 [? [? [? ?]]]]]].
exists m0, m1, m2; auto.
