From Undecidability.Shared.Libs.DLW Require Import utils_tac.
From Undecidability.Synthetic Require Import Undecidability.
Require Import Undecidability.TM.TM.
Require Import Undecidability.PCP.PCP.
Require Import Undecidability.PCP.Reductions.HaltTM_1_to_PCPb.
From Undecidability.MinskyMachines Require Import MM PCPb_to_MM.
From Undecidability.FRACTRAN Require Import FRACTRAN FRACTRAN_undec MM_FRACTRAN.
From Undecidability.H10 Require Import H10 FRACTRAN_DIO.
From Undecidability.H10.Dio Require Import dio_logic dio_elem dio_single.
Import ReductionChainNotations UndecidabilityNotations.
Set Implicit Arguments.
Check FRACTRAN_undec.
Check Hilberts_Tenth.
Check H10_undec.

Theorem DIO_SINGLE_SAT_H10 : DIO_SINGLE_SAT ⪯ H10.
Proof.
apply reduces_dependent; exists.
intros (E,v).
destruct (dio_poly_eq_pos E) as (n & p & q & H).
exists (existT _ n (dp_inst_par _ v p, dp_inst_par _ v q)).
unfold DIO_SINGLE_SAT, H10.
rewrite H.
unfold dio_single_pred.
split; intros (phi & H1); exists phi; revert H1; cbn; rewrite !dp_inst_par_eval; auto.
