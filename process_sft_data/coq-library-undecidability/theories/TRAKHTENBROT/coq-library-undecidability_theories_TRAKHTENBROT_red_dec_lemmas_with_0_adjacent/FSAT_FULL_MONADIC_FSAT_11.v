Require Import List Arith Lia Max.
Require Import Undecidability.Synthetic.Definitions Undecidability.Synthetic.ReducibilityFacts.
Require Import Undecidability.Synthetic.InformativeDefinitions Undecidability.Synthetic.InformativeReducibilityFacts.
From Undecidability.Shared.Libs.DLW.Utils Require Import utils_tac utils_list utils_nat finite.
From Undecidability.Shared.Libs.DLW.Vec Require Import pos vec.
From Undecidability.TRAKHTENBROT Require Import notations utils decidable fol_ops fo_sig fo_terms fo_logic fo_sat fo_sat_dec red_utils Sig_Sig_fin Sig_rem_props Sig_rem_constants Sig0 Sig1 Sig1_1.
Set Implicit Arguments.
Section Sig_MONADIC_Sig_11.
Variable (Σ : fo_signature) (HΣ1 : forall s, ar_syms Σ s <= 1) (HΣ2 : forall r, ar_rels Σ r <= 1).
End Sig_MONADIC_Sig_11.
Section FSAT_MONADIC_DEC.
Variable (F P : Type) (H1 : F -> False) (H2 : discrete P) (A : fol_form (Σ11 F P)).
End FSAT_MONADIC_DEC.
Section FSAT_MONADIC_11_FSAT_MONADIC_1.
Variable (n : nat) (Y : Type) (HY : finite_t Y).
End FSAT_MONADIC_11_FSAT_MONADIC_1.
Section FSAT_Σ11_DEC.
Variable (n : nat) (P : Type) (HP1 : finite_t P) (HP2 : discrete P) (A : fol_form (Σ11 (pos n) P)).
End FSAT_Σ11_DEC.
Section FSAT_FULL_Σ11_DEC.
Variable (F P : Type) (HF : discrete F) (HP : discrete P) (A : fol_form (Σ11 F P)).
Hint Resolve finite_t_pos : core.
End FSAT_FULL_Σ11_DEC.
Section FSAT_FULL_MONADIC_DEC.
Variable (Σ : fo_signature) (H1 : discrete (syms Σ)) (H2 : discrete (rels Σ)) (H3 : forall s, ar_syms Σ s <= 1) (H4 : forall r, ar_rels Σ r <= 1) (A : fol_form Σ).
End FSAT_FULL_MONADIC_DEC.
Section FSAT_PROP_ONLY_DEC.
Variable (Σ : fo_signature) (H1 : discrete (rels Σ)) (H2 : forall r, ar_rels Σ r = 0) (A : fol_form Σ).
End FSAT_PROP_ONLY_DEC.

Theorem FSAT_FULL_MONADIC_FSAT_11 : FSAT Σ ⪯ᵢ FSAT (Σ11 (syms Σ) (rels Σ)).
Proof.
apply ireduces_transitive with (Q := FSAT (Σno_props Σ)).
+
exists (Σrem_props HΣ2 0); intros A.
apply exists_equiv; intro; apply Σrem_props_correct.
+
assert (forall s, ar_syms (Σno_props Σ) s <= 1) as H1.
{
simpl; auto.
}
exists (Σrem_constants H1 0); intros A.
apply exists_equiv; intro; apply Σrem_constants_correct.
