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

Theorem FIN_DISCR_DEC_nSAT_FIN_DEC_2SAT n : @fo_form_fin_discr_dec_SAT (Σrel n) ⪯ᵢ @fo_form_fin_dec_SAT (Σrel 2).
Proof.
exists (@Σn_Σ2_enc n); intros A; split.
+
apply SATn_SAT2.
+
Admitted.

Corollary FSAT_REL_nto2 n : FSAT (Σrel n) ⪯ᵢ FSAT (Σrel 2).
Proof.
apply ireduces_transitive with (1 := FIN_DEC_SAT_FIN_DISCR_DEC_SAT _).
Admitted.

Theorem FSAT_REL2_to_FUNnREL1 n : 2 <= n -> FSAT (Σrel 2) ⪯ᵢ FSAT (Σn1 n).
Proof.
intros Hn; destruct n as [ | [ | n ] ]; try (exfalso; lia); clear Hn.
exists (Σ2_ΣSSn1_enc n); intros A; split.
+
intros (X & M2 & H1 & H2 & phi & H3).
apply Σ2_ΣSSn1_enc_sound with (1 := H3); auto.
+
intros (Y & M21 & H1 & H2 & psi & H3).
Admitted.

Theorem FSAT_FUNnREL1_ANY Σ n f r : ar_syms Σ f = n -> ar_rels Σ r = 1 -> FSAT (Σn1 n) ⪯ᵢ FSAT Σ.
Proof.
intros H1 H2.
apply ireduces_dependent.
intros A.
exists (Σn1_Σ _ _ _ H1 H2 A).
Admitted.

Theorem FSAT_REL_2ton n : 2 <= n -> FSAT (Σrel 2) ⪯ᵢ FSAT (Σrel n).
Proof.
revert n; intros [ | [ | n ] ] H; try (exfalso; lia).
exists (Σ2_Σn n); intros A; split.
+
apply Σ2_Σn_soundness.
+
Admitted.

Theorem FSAT_RELn_ANY Σ n r : ar_rels Σ r = n -> FSAT (Σrel n) ⪯ᵢ FSAT Σ.
Proof.
intros Hr.
destruct (SATn_SAT_reduction _ _ Hr) as (f & Hf).
Admitted.

Let max_syms : { n | forall s, ar_syms Σ s <= n }.
Proof.
destruct HΣ1 as (l & Hl).
exists (lmax (map (ar_syms _) l)).
intros s; apply lmax_prop, in_map_iff.
Admitted.

Let max_rels : { n | forall s, ar_rels Σ s <= n }.
Proof.
destruct HΣ3 as (l & Hl).
exists (lmax (map (ar_rels _) l)).
intros r; apply lmax_prop, in_map_iff.
Admitted.

Theorem FINITARY_TO_BINARY : FSAT Σ ⪯ᵢ FSAT (Σrel 2).
Proof.
destruct max_syms as (ns & Hns).
destruct max_rels as (nr & Hnr).
set (m := lmax (2::(S ns)::nr::nil)).
eapply ireduces_transitive.
{
apply FSAT_Σnosyms; auto.
}
eapply ireduces_transitive.
{
apply FSAT_UNIFORM with (n := m).
intros [ [] | [] ].
+
apply lmax_prop; simpl; auto.
+
apply le_trans with (S ns).
*
simpl; apply le_n_S, Hns.
*
apply lmax_prop; simpl; auto.
+
apply le_trans with nr.
*
simpl; auto.
*
apply lmax_prop; simpl; auto.
}
eapply ireduces_transitive.
{
apply FSAT_ONE_REL; simpl; auto; intros [].
}
eapply ireduces_transitive.
{
apply FSAT_NOCST; simpl; auto.
}
Admitted.

Theorem DISCRETE_TO_BINARY : FSAT Σ ⪯ᵢ FSAT (Σrel 2).
Proof.
apply ireduces_dependent.
intros A.
destruct (Sig_discrete_to_pos HΣ1 HΣ2 A) as (n & m & i & j & B & HB).
destruct (@FINITARY_TO_BINARY (Σpos _ i j)) as (f & Hf); simpl; auto.
exists (f B).
red in Hf.
Admitted.

Let discrete_bpcp_syms : discrete Σbpcp_syms.
Proof.
Admitted.

Let finite_t_bpcp_rels : finite_t Σbpcp_rels.
Proof.
exists (Σbpcp_hand::Σbpcp_ssfx::Σbpcp_eq::nil).
Admitted.

Let discrete_bpcp_rels : discrete Σbpcp_rels.
Proof.
Admitted.

Let BPCP_Sig2 : BPCP_problem ⪯ᵢ FSAT (Σrel 2).
Proof.
apply ireduces_transitive with (1 := BPCP_FSAT_Σbpcp).
Admitted.

Theorem FULL_TRAKHTENBROT Σ : { r | 2 <= ar_rels Σ r } + { f : _ & { r | 2 <= ar_syms Σ f /\ ar_rels Σ r = 1 } } -> BPCP_problem ⪯ᵢ FSAT Σ.
Proof.
intros H.
apply ireduces_transitive with (1 := BPCP_Sig2).
revert H; intros [ (r & Hr) | (f & r & Hf & Hr) ].
+
apply ireduces_transitive with (1 := FSAT_REL_2ton Hr).
apply FSAT_RELn_ANY with (1 := eq_refl).
+
apply ireduces_transitive with (1 := FSAT_REL2_to_FUNnREL1 Hf).
Admitted.

Corollary FULL_TRAKHTENBROT_non_informative Σ : (exists r, 2 <= ar_rels Σ r) \/ (exists f r, 2 <= ar_syms Σ f /\ ar_rels Σ r = 1) -> BPCP_problem ⪯ FSAT Σ.
Proof.
Admitted.

Let finite_t_bpcp_syms : finite_t Σbpcp_syms.
Proof.
exists (Σbpcp_bool true::Σbpcp_bool false::Σbpcp_unit::Σbpcp_undef::nil).
intros [ [] | | ]; simpl; auto.
