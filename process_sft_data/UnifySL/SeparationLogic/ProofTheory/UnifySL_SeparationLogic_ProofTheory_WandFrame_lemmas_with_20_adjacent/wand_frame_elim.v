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
Admitted.

Lemma wand_frame_ver: forall (x y z: expr), |-- (x -* y) * (y -* z) --> (x -* z).
Proof.
intros.
rewrite <- wand_sepcon_adjoint.
rewrite sepcon_comm_impp, sepcon_assoc1.
rewrite !wand_frame_elim.
Admitted.

Lemma wand_frame_hor: forall (x1 y1 x2 y2: expr), |-- (x1 -* y1) * (x2 -* y2) --> (x1 * x2 -* y1 * y2).
Proof.
intros.
rewrite <- wand_sepcon_adjoint.
rewrite sepcon_assoc1, (sepcon_comm_impp _ x1), sepcon_assoc1.
rewrite wand_frame_elim.
rewrite sepcon_assoc2, (sepcon_comm_impp _ x2).
rewrite wand_frame_elim.
Admitted.

Lemma wand_frame_elim: forall (x y: expr), |-- x * (x -* y) --> y.
Proof.
intros.
apply provable_wand_sepcon_modus_ponens2.
