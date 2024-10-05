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

Theorem Hilberts_Tenth : ⎩ HaltTM 1 ⪯ₘ PCPb ⪯ₘ MM_HALTING ⪯ₘ FRACTRAN_HALTING ⪯ₘ DIO_LOGIC_SAT ⪯ₘ DIO_ELEM_SAT ⪯ₘ DIO_SINGLE_SAT ⪯ₘ H10 ⎭.
Proof.
msplit 6.
+
apply HaltTM_1_to_PCPb.
+
apply PCPb_MM_HALTING.
+
apply MM_FRACTRAN_HALTING.
+
apply FRACTRAN_HALTING_DIO_LOGIC_SAT.
+
apply DIO_LOGIC_ELEM_SAT.
+
apply DIO_ELEM_SINGLE_SAT.
+
apply DIO_SINGLE_SAT_H10.
