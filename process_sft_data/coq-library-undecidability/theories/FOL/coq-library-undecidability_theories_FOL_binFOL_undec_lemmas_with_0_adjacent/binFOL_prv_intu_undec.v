Require Import Undecidability.Synthetic.Definitions Undecidability.Synthetic.Undecidability.
Require Import Undecidability.PCP.PCP_undec.
Require Import Undecidability.FOL.binFOL.
From Undecidability.FOL Require Import binZF_undec binZF Util.FullTarski_facts Util.FullDeduction_facts.

Lemma binFOL_prv_intu_undec : undecidable binFOL_prv_intu.
Proof.
apply (undecidability_from_reducibility undecidable_deduction_binZF), binZF_binFOL_prv_intu.
