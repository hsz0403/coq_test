Require Import Coq.Logic.Classical_Prop.
Require Import Logic.lib.Ensembles_ext.
Require Import Logic.GeneralLogic.Base.
Require Import Logic.MinimumLogic.Syntax.
Require Import Logic.MinimumLogic.Semantics.Trivial.
Local Open Scope logic_base.
Local Open Scope syntax.
Section Sound.
Context {L: Language} {minL: MinimumLanguage L} {MD: Model} {SM: Semantics L MD} {tminSM: TrivialMinimumSemantics L MD SM}.
End Sound.

Lemma sound_axiom2: forall x y z m, m |= (x --> y --> z) --> (x --> y) --> (x --> z).
Proof.
intros.
rewrite !sat_impp.
intros ? ? ?.
specialize (H H1).
specialize (H0 H1).
auto.
