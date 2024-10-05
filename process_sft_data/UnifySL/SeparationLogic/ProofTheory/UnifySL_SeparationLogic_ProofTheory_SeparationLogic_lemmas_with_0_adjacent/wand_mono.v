Require Import Logic.GeneralLogic.Base.
Require Import Logic.GeneralLogic.ProofTheory.BasicSequentCalculus.
Require Import Logic.MinimumLogic.Syntax.
Require Import Logic.MinimumLogic.ProofTheory.Minimum.
Require Import Logic.MinimumLogic.ProofTheory.ProofTheoryPatterns.
Require Import Logic.MinimumLogic.ProofTheory.RewriteClass.
Require Import Logic.PropositionalLogic.Syntax.
Require Import Logic.PropositionalLogic.ProofTheory.Intuitionistic.
Require Import Logic.PropositionalLogic.ProofTheory.DeMorgan.
Require Import Logic.PropositionalLogic.ProofTheory.GodelDummett.
Require Import Logic.PropositionalLogic.ProofTheory.Classical.
Require Import Logic.PropositionalLogic.ProofTheory.RewriteClass.
Require Import Logic.PropositionalLogic.ProofTheory.ProofTheoryPatterns.
Require Import Logic.SeparationLogic.Syntax.
Local Open Scope logic_base.
Local Open Scope syntax.
Import PropositionalLanguageNotation.
Import SeparationLogicNotation.
Class SepconAxiomatization (L: Language) {minL: MinimumLanguage L} {sepconL: SepconLanguage L} (Gamma: Provable L) := { sepcon_comm_impp: forall x y, |-- x * y --> y * x; sepcon_assoc1: forall x y z, |-- x * (y * z) --> (x * y) * z; sepcon_mono: forall x1 x2 y1 y2, |-- x1 --> x2 -> |-- y1 --> y2 -> |-- (x1 * y1) --> (x2 * y2); }.
Class SepconOrAxiomatization (L: Language) {minL: MinimumLanguage L} {pL: PropositionalLanguage L} {sepconL: SepconLanguage L} (Gamma: Provable L) := { orp_sepcon_left: forall (x y z: expr), |-- (x || y) * z --> x * z || y * z }.
Class SepconFalseAxiomatization (L: Language) {minL: MinimumLanguage L} {pL: PropositionalLanguage L} {sepconL: SepconLanguage L} (Gamma: Provable L) := { falsep_sepcon_left: forall (x: expr), |-- FF * x --> FF }.
Class EmpAxiomatization (L: Language) {minL: MinimumLanguage L} {sepconL: SepconLanguage L} {empL: EmpLanguage L} (Gamma: Provable L) := { sepcon_emp1: forall x, |-- x * emp --> x; sepcon_emp2: forall x, |-- x --> x * emp }.
Class WandAxiomatization (L: Language) {minL: MinimumLanguage L} {sepconL: SepconLanguage L} {wandL: WandLanguage L} (Gamma: Provable L) := { wand_sepcon_adjoint: forall x y z, |-- x * y --> z <-> |-- x --> (y -* z) }.
Class ExtSeparationLogic (L: Language) {minL: MinimumLanguage L} {pL: PropositionalLanguage L} {sepconL: SepconLanguage L} (Gamma: Provable L) := { sepcon_ext: forall x, |-- x --> x * TT }.
Class NonsplitEmpSeparationLogic (L: Language) {minL: MinimumLanguage L} {pL: PropositionalLanguage L} {sepconL: SepconLanguage L} {empL: EmpLanguage L} (Gamma: Provable L) := { emp_sepcon_truep_elim: forall x, |-- (x * TT) && emp --> x }.
Class DupEmpSeparationLogic (L: Language) {minL: MinimumLanguage L} {pL: PropositionalLanguage L} {sepconL: SepconLanguage L} {empL: EmpLanguage L} (Gamma: Provable L) := { emp_dup: forall x, |-- x && emp --> x * x }.
Class MallocFreeSeparationLogic (L: Language) {minL: MinimumLanguage L} {pL: PropositionalLanguage L} {sepconL: SepconLanguage L} {empL: EmpLanguage L} (Gamma: Provable L) := { MallocFreeSeparationLogic_NonsplitEmpSeparationLogic :> NonsplitEmpSeparationLogic L Gamma; MallocFreeSeparationLogic_DupEmpSeparationLogic :> DupEmpSeparationLogic L Gamma }.
Class GarbageCollectSeparationLogic (L: Language) {minL: MinimumLanguage L} {pL: PropositionalLanguage L} {sepconL: SepconLanguage L} (Gamma: Provable L) := { sepcon_elim1: forall x y, |-- x * y --> x }.
Section SepconRules.
Context {L: Language} {minL: MinimumLanguage L} {sepconL: SepconLanguage L} {Gamma: Provable L} {minAX: MinimumAxiomatization L Gamma} {sepconAX: SepconAxiomatization L Gamma}.
Context {pL: PropositionalLanguage L} {ipAX: IntuitionisticPropositionalLogic L Gamma}.
Context {sepcon_orp_AX: SepconOrAxiomatization L Gamma} {sepcon_false_AX: SepconFalseAxiomatization L Gamma}.
Context {empL: EmpLanguage L} {empAX: EmpAxiomatization L Gamma}.
End SepconRules.
Section WandRules.
Context {L: Language} {minL: MinimumLanguage L} {sepconL: SepconLanguage L} {wandL: WandLanguage L} {Gamma: Provable L} {minAX: MinimumAxiomatization L Gamma} {wandX: WandAxiomatization L Gamma}.
Context {sepconAX: SepconAxiomatization L Gamma}.
Context {pL: PropositionalLanguage L} {ipAX: IntuitionisticPropositionalLogic L Gamma} {sepcon_orp_AX: SepconOrAxiomatization L Gamma} {sepcon_false_AX: SepconFalseAxiomatization L Gamma}.
End WandRules.

Lemma wand_mono: forall x1 x2 y1 y2, |-- x2 --> x1 -> |-- y1 --> y2 -> |-- (x1 -* y1) --> (x2 -* y2).
Proof.
intros.
apply (@funcp_mono _ _ _ _ _ _ wand_sepcon_Adj sepcon_Mono); auto.
