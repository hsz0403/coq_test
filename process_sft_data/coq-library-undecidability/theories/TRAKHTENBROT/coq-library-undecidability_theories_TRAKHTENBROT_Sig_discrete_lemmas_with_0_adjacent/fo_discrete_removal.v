Require Import List Arith Lia.
From Undecidability.Shared.Libs.DLW.Utils Require Import utils_tac utils_list finite.
From Undecidability.Shared.Libs.DLW.Vec Require Import pos vec.
From Undecidability.TRAKHTENBROT Require Import notations fol_ops fo_sig fo_terms fo_logic fo_sat discrete.
Set Implicit Arguments.

Theorem fo_discrete_removal Σ (A : fol_form Σ) : fo_form_fin_dec_SAT A -> exists n, fo_form_fin_discr_dec_SAT_in A (pos n).
Proof.
intros (X & M & Hfin & Hdec & phi & HA).
set (ls := fol_syms A).
set (lr := fol_rels A).
destruct (fo_fin_model_discretize ls lr Hfin Hdec) as (n & Md & Mdec & f & E).
set (psy n := f (phi n)).
exists n, (@pos_eq_dec _), Md, (finite_t_pos _) , Mdec, psy.
revert HA.
apply fo_model_projection with (p := f); unfold lr, ls; auto; apply incl_refl.
