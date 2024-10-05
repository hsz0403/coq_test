Require Import List Arith Lia.
From Undecidability.Shared.Libs.DLW.Utils Require Import utils_tac utils_list finite.
From Undecidability.Shared.Libs.DLW.Vec Require Import pos vec.
From Undecidability.TRAKHTENBROT Require Import notations fol_ops fo_sig fo_terms fo_logic fo_sat discrete.
Set Implicit Arguments.

Theorem fo_form_fin_dec_SAT_fin_discr_dec Σ (A : fol_form Σ) : fo_form_fin_dec_SAT A -> fo_form_fin_discr_dec_SAT A.
Proof.
intros H.
destruct fo_discrete_removal with (1 := H) (A := A) as (n & Hn); auto.
exists (pos n); auto.
