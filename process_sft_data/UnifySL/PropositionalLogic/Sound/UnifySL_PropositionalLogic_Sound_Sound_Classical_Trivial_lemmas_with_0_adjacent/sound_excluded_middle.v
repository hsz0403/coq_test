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

Lemma sound_excluded_middle: forall x m, m |= x || (x --> FF).
Proof.
intros.
rewrite sat_orp, sat_impp, sat_falsep.
tauto.
