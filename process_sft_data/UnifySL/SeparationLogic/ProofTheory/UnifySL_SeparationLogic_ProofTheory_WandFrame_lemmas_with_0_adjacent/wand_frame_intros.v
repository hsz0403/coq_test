Require Import Logic.lib.Coqlib.
Require Import Logic.GeneralLogic.Base.
Require Import Logic.GeneralLogic.ProofTheory.BasicSequentCalculus.
Require Import Logic.MinimumLogic.Syntax.
Require Import Logic.MinimumLogic.ProofTheory.Minimum.
Require Import Logic.MinimumLogic.ProofTheory.RewriteClass.
Require Import Logic.PropositionalLogic.Syntax.
Require Import Logic.PropositionalLogic.ProofTheory.Intuitionistic.
Require Import Logic.PropositionalLogic.ProofTheory.DeMorgan.
Require Import Logic.PropositionalLogic.ProofTheory.GodelDummett.
Require Import Logic.PropositionalLogic.ProofTheory.Classical.
Require Import Logic.PropositionalLogic.ProofTheory.RewriteClass.
Require Import Logic.SeparationLogic.Syntax.
Require Import Logic.SeparationLogic.ProofTheory.SeparationLogic.
Require Import Logic.SeparationLogic.ProofTheory.RewriteClass.
Local Open Scope logic_base.
Local Open Scope syntax.
Import PropositionalLanguageNotation.
Import SeparationLogicNotation.
Section WandFrame.
Context {L: Language} {minL: MinimumLanguage L} {sepconL: SepconLanguage L} {wandL: WandLanguage L} {Gamma: Provable L} {minAX: MinimumAxiomatization L Gamma} {sepconAX: SepconAxiomatization L Gamma} {wandAX: WandAxiomatization L Gamma}.
End WandFrame.

Lemma wand_frame_intros: forall (x y: expr), |-- x --> (y -* x * y).
Proof.
intros.
apply wand_sepcon_adjoint.
apply provable_impp_refl.
