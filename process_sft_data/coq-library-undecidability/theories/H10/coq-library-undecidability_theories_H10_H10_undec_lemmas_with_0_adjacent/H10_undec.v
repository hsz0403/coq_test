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

Theorem H10_undec : undecidable H10.
Proof.
apply (undecidability_from_reducibility undecidability_HaltTM).
reduce with chain Hilberts_Tenth.
