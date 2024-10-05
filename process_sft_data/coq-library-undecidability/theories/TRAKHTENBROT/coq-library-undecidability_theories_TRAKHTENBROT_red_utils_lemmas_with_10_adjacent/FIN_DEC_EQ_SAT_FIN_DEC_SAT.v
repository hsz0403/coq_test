Require Import List Arith Bool Lia Eqdep_dec.
Require Import Undecidability.Synthetic.Definitions Undecidability.Synthetic.ReducibilityFacts.
Require Import Undecidability.Synthetic.InformativeDefinitions Undecidability.Synthetic.InformativeReducibilityFacts.
From Undecidability.PCP Require Import PCP.
From Undecidability.Shared.Libs.DLW.Utils Require Import utils_tac utils_list utils_nat finite.
From Undecidability.Shared.Libs.DLW.Vec Require Import pos vec.
From Undecidability.TRAKHTENBROT Require Import notations bpcp fo_sig fo_terms fo_logic fo_sat Sig_discrete (* UTILITY: discrete <-> non discrete *) Sig_noeq (* UTILITY: from interpreted to uninterpreted *) .
Set Implicit Arguments.
Definition FSAT := @fo_form_fin_dec_SAT.
Arguments FSAT : clear implicits.
Section FIN_DEC_EQ_SAT_FIN_DEC_SAT.
Variable (Σ : fo_signature) (e : rels Σ) (He : ar_rels _ e = 2).
End FIN_DEC_EQ_SAT_FIN_DEC_SAT.

Theorem BPCP_BPCP_problem_eq R : BPCP_problem R <-> BPCP R.
Proof.
split; intros (u & Hu).
+
constructor 1 with u; auto.
+
Admitted.

Theorem BPCP_BPCP_problem : BPCP ⪯ᵢ BPCP_problem.
Proof.
Admitted.

Theorem fo_form_fin_dec_SAT_discr_equiv Σ A : @fo_form_fin_dec_SAT Σ A <-> @fo_form_fin_discr_dec_SAT Σ A.
Proof.
split.
+
apply fo_form_fin_dec_SAT_fin_discr_dec.
+
Admitted.

Corollary FIN_DEC_SAT_FIN_DISCR_DEC_SAT Σ : FSAT Σ ⪯ᵢ @fo_form_fin_discr_dec_SAT Σ.
Proof.
Admitted.

Theorem FIN_DEC_EQ_SAT_FIN_DEC_SAT : fo_form_fin_dec_eq_SAT e He ⪯ᵢ FSAT Σ.
Proof.
exists (fun A => Σ_noeq (fol_syms A) (e::fol_rels A) _ He A).
intros A; split.
+
intros (X & HX); exists X; revert HX.
apply Σ_noeq_sound.
+
apply Σ_noeq_complete; cbv; auto.
