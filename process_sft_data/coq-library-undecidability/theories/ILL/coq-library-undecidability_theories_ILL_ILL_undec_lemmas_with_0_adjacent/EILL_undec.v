From Undecidability.Shared.Libs.DLW Require Import utils_tac.
Require Import Undecidability.Synthetic.Undecidability.
From Undecidability.PCP Require Import PCP PCP_undec.
From Undecidability.StackMachines Require Import BSM.
From Undecidability.MinskyMachines Require Import MM.
From Undecidability.ILL Require Import EILL ILL iBPCP_MM MM_EILL EILL_ILL.
Require Import Undecidability.PCP.Reductions.HaltTM_1_to_PCPb.
Import ReductionChainNotations UndecidabilityNotations.
Check PCP_chain_ILL.
Local Hint Resolve EILL_rILL_cf_PROVABILITY EILL_rILL_PROVABILITY EILL_ILL_cf_PROVABILITY : core.

Theorem EILL_undec : undecidable EILL_PROVABILITY.
Proof.
undec from PCP_undec using chain PCP_chain_ILL.
