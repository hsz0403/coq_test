Require Import Coq.Logic.Classical_Prop.
Require Import Logic.lib.Ensembles_ext.
Require Import Logic.GeneralLogic.Base.
Require Import Logic.MinimumLogic.Syntax.
Require Import Logic.MinimumLogic.Semantics.Trivial.
Require Import Logic.PropositionalLogic.Syntax.
Require Import Logic.PropositionalLogic.Semantics.Trivial.
Local Open Scope logic_base.
Local Open Scope syntax.
Import PropositionalLanguageNotation.
Section Sound.
Context {L: Language} {minL: MinimumLanguage L} {pL: PropositionalLanguage L} {MD: Model} {SM: Semantics L MD} {tminSM: TrivialMinimumSemantics L MD SM} {tpSM: TrivialPropositionalSemantics L MD SM}.
End Sound.

Lemma sound_andp_elim1: forall x y m, m |= x && y --> x.
Proof.
intros.
rewrite !sat_impp, sat_andp.
intros [? ?].
auto.
