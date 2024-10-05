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
Require Import Logic.SeparationLogic.Semantics.FlatSemantics.
Local Open Scope logic_base.
Local Open Scope syntax.
Local Open Scope kripke_model.
Import PropositionalLanguageNotation.
Import SeparationLogicNotation.
Import KripkeModelFamilyNotation.
Import KripkeModelNotation_Intuitionistic.
Section Sound_Flat.
Context {L: Language} {minL: MinimumLanguage L} {pL: PropositionalLanguage L} {sepconL: SepconLanguage L} {wandL: WandLanguage L} {MD: Model} {kMD: KripkeModel MD} (M: Kmodel) {R: Relation (Kworlds M)} {po_R: PreOrder Krelation} {J: Join (Kworlds M)} {SA: SeparationAlgebra (Kworlds M)} {dSA: DownwardsClosedSeparationAlgebra (Kworlds M)} {SM: Semantics L MD} {kiSM: KripkeIntuitionisticSemantics L MD M SM} {kminSM: KripkeMinimumSemantics L MD M SM} {kpSM: KripkePropositionalSemantics L MD M SM} {fsepconSM: FlatSemantics.SepconSemantics L MD M SM} {fwandSM: FlatSemantics.WandSemantics L MD M SM}.
Context {empL: EmpLanguage L} {feSM: EmpSemantics L MD M SM}.
End Sound_Flat.

Lemma sound_sepcon_emp2 {USA: UnitalSeparationAlgebra (Kworlds M)}: forall x: expr, forall m, KRIPKE: M, m |= x --> x * emp.
Proof.
intros.
rewrite sat_impp; intros.
rewrite sat_sepcon.
destruct (incr_exists n) as [u [? ?]].
destruct H1 as [n' [H1 H1']].
exists n', u.
split; [| split]; auto.
+
apply join_comm; auto.
+
eapply sat_mono; eauto.
+
rewrite sat_emp; auto.
