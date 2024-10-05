Require Import Undecidability.Synthetic.Definitions Undecidability.Synthetic.Undecidability.
Require Import Undecidability.PCP.PCP_undec.
Require Import Undecidability.FOL.binFOL.
From Undecidability.FOL Require Import binZF_undec binZF Util.FullTarski_facts Util.FullDeduction_facts.

Lemma binZF_binFOL_prv_intu : deduction_binZF ⪯ binFOL_prv_intu.
Proof.
exists (impl binZF).
intros phi.
unfold binFOL_prv_intu, deduction_binZF.
setoid_rewrite <- impl_prv.
rewrite List.app_nil_r.
split; intros H; apply (Weak H); unfold List.incl; apply List.in_rev.
