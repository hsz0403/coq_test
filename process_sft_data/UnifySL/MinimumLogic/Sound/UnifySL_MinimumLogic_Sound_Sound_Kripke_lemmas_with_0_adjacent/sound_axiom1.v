Require Import Coq.Logic.Classical_Prop.
Require Import Coq.Logic.Classical_Pred_Type.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Relations.Relation_Definitions.
Require Import Logic.GeneralLogic.Base.
Require Import Logic.GeneralLogic.KripkeModel.
Require Import Logic.GeneralLogic.Semantics.Kripke.
Require Import Logic.MinimumLogic.Syntax.
Require Import Logic.MinimumLogic.Semantics.Kripke.
Local Open Scope logic_base.
Local Open Scope syntax.
Local Open Scope kripke_model.
Import KripkeModelFamilyNotation.
Import KripkeModelNotation_Intuitionistic.
Section Sound_Kripke.
Context {L: Language} {minL: MinimumLanguage L} {MD: Model} {kMD: KripkeModel MD} {M: Kmodel} {R: Relation (Kworlds M)} {po_R: PreOrder Krelation} {SM: Semantics L MD} {kiSM: KripkeIntuitionisticSemantics L MD M SM} {kminSM: KripkeMinimumSemantics L MD M SM}.
End Sound_Kripke.

Lemma sound_axiom1: forall x y: expr, forall m, KRIPKE: M, m |= x --> y --> x.
Proof.
intros.
rewrite sat_impp; intros.
rewrite sat_impp; intros.
eapply sat_mono; eauto.
