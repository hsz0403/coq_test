Require Import Undecidability.Synthetic.Definitions Undecidability.Synthetic.Undecidability.
Require Import Undecidability.PCP.PCP_undec.
Require Import Undecidability.FOL.binFOL.
From Undecidability.FOL Require Import binZF_undec binZF Util.FullTarski_facts Util.FullDeduction_facts.

Lemma binZF_binFOL_valid : entailment_binZF ⪯ binFOL_valid.
Proof.
exists (impl binZF).
intros phi.
unfold binFOL_valid, valid, entailment_binZF.
setoid_rewrite impl_sat.
reflexivity.
