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

Lemma sepcon_Comm: Commutativity L Gamma sepcon.
Proof.
constructor.
intros.
Admitted.

Lemma sepcon_Assoc: Associativity L Gamma sepcon.
Proof.
apply @Build_Associativity1; auto.
+
apply sepcon_Comm.
+
apply sepcon_Mono.
+
intros.
Admitted.

Lemma sepcon_assoc2: forall x y z, |-- (x * y) * z --> x * (y * z).
Proof.
intros.
Admitted.

Lemma sepcon_comm: forall (x y: expr), |-- x * y <--> y * x.
Proof.
intros.
Admitted.

Lemma sepcon_assoc: forall x y z, |-- x * (y * z) <--> (x * y) * z.
Proof.
intros.
Admitted.

Lemma orp_sepcon_right: forall (x y z: expr), |-- x * z || y * z --> (x || y) * z.
Proof.
intros.
apply solve_orp_impp; apply sepcon_mono.
-
apply orp_intros1.
-
apply provable_impp_refl.
-
apply orp_intros2.
-
Admitted.

Lemma falsep_sepcon_right: forall (x: expr),|-- FF --> FF * x.
Proof.
intros.
Admitted.

Lemma sepcon_orp_RDistr: RightDistr L Gamma sepcon orp.
Proof.
constructor; intros.
+
apply orp_sepcon_left.
+
Admitted.

Lemma sepcon_orp_LDistr: LeftDistr L Gamma sepcon orp.
Proof.
apply @RightDistr2LeftDistr; auto.
+
apply sepcon_Comm.
+
apply orp_Mono.
+
Admitted.

Lemma sepcon_orp_distr_r: forall (x y z: expr), |-- (x || y) * z <--> x * z || y * z.
Proof.
intros.
Admitted.

Lemma sepcon_orp_distr_l: forall (x y z: expr), |-- x * (y || z) <--> x * y || x * z.
Proof.
intros.
Admitted.

Lemma sepcon_Mono: Monotonicity L Gamma sepcon.
Proof.
constructor.
intros.
apply sepcon_mono; auto.
