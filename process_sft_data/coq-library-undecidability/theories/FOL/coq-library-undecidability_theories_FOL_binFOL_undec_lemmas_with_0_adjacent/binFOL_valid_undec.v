Require Import Undecidability.Synthetic.Definitions Undecidability.Synthetic.Undecidability.
Require Import Undecidability.PCP.PCP_undec.
Require Import Undecidability.FOL.binFOL.
From Undecidability.FOL Require Import binZF_undec binZF Util.FullTarski_facts Util.FullDeduction_facts.

Lemma binFOL_valid_undec : undecidable binFOL_valid.
Proof.
apply (undecidability_from_reducibility undecidable_entailment_binZF), binZF_binFOL_valid.
