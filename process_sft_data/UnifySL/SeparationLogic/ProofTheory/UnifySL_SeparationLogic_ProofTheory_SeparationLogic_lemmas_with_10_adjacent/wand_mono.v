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

Lemma sepcon_orp_distr_r: forall (x y z: expr), |-- (x || y) * z <--> x * z || y * z.
Proof.
intros.
Admitted.

Lemma sepcon_orp_distr_l: forall (x y z: expr), |-- x * (y || z) <--> x * y || x * z.
Proof.
intros.
Admitted.

Lemma falsep_sepcon: forall (x: expr), |-- FF * x <--> FF.
Proof.
intros.
apply solve_andp_intros.
+
apply falsep_sepcon_left.
+
Admitted.

Lemma sepcon_falsep: forall (x: expr), |-- x * FF <--> FF.
Proof.
intros.
rewrite sepcon_comm.
Admitted.

Lemma sepcon_emp: forall x, |-- x * emp <--> x.
Proof.
intros.
apply solve_andp_intros.
+
apply sepcon_emp1.
+
Admitted.

Lemma sepcon_LU: LeftUnit L Gamma emp sepcon.
Proof.
apply Build_LeftUnit'.
intros.
rewrite sepcon_comm.
Admitted.

Lemma sepcon_RU: RightUnit L Gamma emp sepcon.
Proof.
apply Build_RightUnit'.
intros.
Admitted.

Lemma wand_sepcon_Adj: Adjointness L Gamma sepcon wand.
Proof.
constructor.
intros.
Admitted.

Lemma provable_wand_sepcon_modus_ponens1: forall (x y: expr), |-- (x -* y) * x --> y.
Proof.
intros.
Admitted.

Lemma provable_wand_sepcon_modus_ponens2: forall (x y: expr), |-- x * (x -* y) --> y.
Proof.
intros.
rewrite (sepcon_comm_impp x (x -* y)).
Admitted.

Lemma wand_andp: forall x y z: expr, |-- x -* y && z <--> (x -* y) && (x -* z).
Proof.
intros.
Admitted.

Lemma orp_wand: forall x y z: expr, |-- (x || y) -* z <--> (x -* z) && (y -* z).
Proof.
intros.
Admitted.

Lemma sepcon_elim2: forall {gcsGamma: GarbageCollectSeparationLogic L Gamma} (x y: expr), |-- x * y --> y.
Proof.
intros.
rewrite (sepcon_comm x y).
Admitted.

Lemma emp_sepcon_elim1: forall {empL: EmpLanguage L} {empAX: EmpAxiomatization L Gamma} {nssGamma: NonsplitEmpSeparationLogic L Gamma} x y, |-- x * y && emp --> x.
Proof.
intros.
rewrite <- (emp_sepcon_truep_elim x) at 2.
apply andp_proper_impp; [| apply provable_impp_refl].
apply sepcon_mono; [apply provable_impp_refl |].
Admitted.

Lemma emp_sepcon_elim2: forall {empL: EmpLanguage L} {empAX: EmpAxiomatization L Gamma} {nssGamma: NonsplitEmpSeparationLogic L Gamma} x y, |-- x * y && emp --> y.
Proof.
intros.
rewrite sepcon_comm.
Admitted.

Lemma wand_mono: forall x1 x2 y1 y2, |-- x2 --> x1 -> |-- y1 --> y2 -> |-- (x1 -* y1) --> (x2 -* y2).
Proof.
intros.
apply (@funcp_mono _ _ _ _ _ _ wand_sepcon_Adj sepcon_Mono); auto.
