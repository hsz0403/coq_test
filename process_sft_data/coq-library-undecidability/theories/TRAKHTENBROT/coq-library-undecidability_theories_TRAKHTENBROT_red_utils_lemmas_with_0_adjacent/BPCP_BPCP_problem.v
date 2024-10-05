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

Theorem BPCP_BPCP_problem : BPCP ⪯ᵢ BPCP_problem.
Proof.
exists (fun x => x); red; symmetry; apply BPCP_BPCP_problem_eq.
