Require Import List Arith Bool Lia Eqdep_dec.
Require Import Undecidability.Synthetic.Definitions Undecidability.Synthetic.ReducibilityFacts.
Require Import Undecidability.Synthetic.InformativeDefinitions Undecidability.Synthetic.InformativeReducibilityFacts.
From Undecidability.Shared.Libs.DLW.Utils Require Import utils_tac utils_list utils_nat finite.
From Undecidability.Shared.Libs.DLW.Vec Require Import pos vec.
From Undecidability.Shared.Libs.DLW.Wf Require Import wf_finite.
From Undecidability.TRAKHTENBROT Require Import notations utils decidable bpcp fo_sig fo_terms fo_logic fo_sat red_utils Sig_discrete BPCP_SigBPCP (* from BPCP to a finitary signature *) Sig_rem_syms (* convert symbols into rels *) Sig_uniform (* convert to same arity for every rels *) Sig_one_rel (* many rels of arity n into one (n+1) and constants *) Sig_rem_cst (* replace constants with free variables *) Sign_Sig2 (* From R_n to R_2 *) Sig2_Sign (* Embed R_2 into R_n with n >= 2 *) Sign_Sig (* Embed R_n into Σ where R_n occurs in Σ *) Sig_Sig_fin (* Alternate path: Σ -> Σfin -> Σ2 *) Sig2_SigSSn1 (* Embed Σ2 = (ø,{R_2}) into ΣSSn1 = ({f_(2+n)},{P_1}) *) Sign1_Sig (* Embed Σn1 = ({f_n},{R_1}) into Σ where f_n and R_1 occur into Σ *) .
Set Implicit Arguments.
Section BPCP_fo_fin_dec_SAT.
Definition FIN_SAT_input := fol_form Σbpcp.
End BPCP_fo_fin_dec_SAT.
Section FIN_DISCR_DEC_SAT_FIN_DEC_EQ_NOSYMS_SAT.
Variable (Σ : fo_signature) (HΣ : finite_t (syms Σ) + discrete (syms Σ)).
End FIN_DISCR_DEC_SAT_FIN_DEC_EQ_NOSYMS_SAT.
Section FINITARY_TO_BINARY.
Variable (Σ : fo_signature) (HΣ1 : finite_t (syms Σ)) (HΣ2 : discrete (syms Σ)) (HΣ3 : finite_t (rels Σ)) (HΣ4 : discrete (rels Σ)).
Let max_syms : { n | forall s, ar_syms Σ s <= n }.
Proof.
destruct HΣ1 as (l & Hl).
exists (lmax (map (ar_syms _) l)).
intros s; apply lmax_prop, in_map_iff.
exists s; auto.
Let max_rels : { n | forall s, ar_rels Σ s <= n }.
Proof.
destruct HΣ3 as (l & Hl).
exists (lmax (map (ar_rels _) l)).
intros r; apply lmax_prop, in_map_iff.
exists r; auto.
Hint Resolve finite_t_sum finite_sum finite_t_finite finite_t_unit : core.
End FINITARY_TO_BINARY.
Section DISCRETE_TO_BINARY.
Variable (Σ : fo_signature) (HΣ1 : discrete (syms Σ)) (HΣ2 : discrete (rels Σ)).
Hint Resolve finite_t_pos : core.
End DISCRETE_TO_BINARY.
Section FULL_TRAKHTENBROT.
Let finite_t_bpcp_syms : finite_t Σbpcp_syms.
Proof.
exists (Σbpcp_bool true::Σbpcp_bool false::Σbpcp_unit::Σbpcp_undef::nil).
intros [ [] | | ]; simpl; auto.
Let discrete_bpcp_syms : discrete Σbpcp_syms.
Proof.
unfold discrete, decidable; repeat decide equality.
Let finite_t_bpcp_rels : finite_t Σbpcp_rels.
Proof.
exists (Σbpcp_hand::Σbpcp_ssfx::Σbpcp_eq::nil).
intros []; simpl; auto.
Let discrete_bpcp_rels : discrete Σbpcp_rels.
Proof.
unfold discrete, decidable; repeat decide equality.
Let BPCP_Sig2 : BPCP_problem ⪯ᵢ FSAT (Σrel 2).
Proof.
apply ireduces_transitive with (1 := BPCP_FSAT_Σbpcp).
apply FINITARY_TO_BINARY; auto.
End FULL_TRAKHTENBROT.

Let max_rels : { n | forall s, ar_rels Σ s <= n }.
Proof.
destruct HΣ3 as (l & Hl).
exists (lmax (map (ar_rels _) l)).
intros r; apply lmax_prop, in_map_iff.
exists r; auto.
