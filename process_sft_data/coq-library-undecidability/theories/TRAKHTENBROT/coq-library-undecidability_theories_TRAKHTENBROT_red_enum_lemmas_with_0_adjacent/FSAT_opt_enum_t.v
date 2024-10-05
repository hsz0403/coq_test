Require Import List Arith Lia Max.
From Undecidability.Shared.Libs.DLW.Utils Require Import utils_tac utils_list utils_nat finite.
From Undecidability.Shared.Libs.DLW.Vec Require Import pos vec.
From Undecidability.TRAKHTENBROT Require Import notations utils enumerable fol_ops fo_sig fo_terms fo_logic fo_enum decidable fo_sat fo_sat_dec red_utils.
Set Implicit Arguments.
Section FSAT_enumerable.
Variable (Σ : fo_signature).
Implicit Type (A : fol_form Σ).
Hypothesis (H1 : discrete (syms Σ)) (H2 : discrete (rels Σ)).
Let dec n A : decidable (fo_form_fin_dec_SAT_in A (pos n)).
Proof.
apply FSAT_in_dec; auto; apply finite_t_pos.
Hypothesis (H3 : type_enum_t (syms Σ)).
Hypothesis (H4 : type_enum_t (rels Σ)).
End FSAT_enumerable.

Theorem FSAT_opt_enum_t : opt_enum_t (FSAT Σ).
Proof.
generalize FSAT_rec_enum_t.
apply rec_enum_opt_enum_type_enum_t.
apply type_enum_t_fol_form; auto.
