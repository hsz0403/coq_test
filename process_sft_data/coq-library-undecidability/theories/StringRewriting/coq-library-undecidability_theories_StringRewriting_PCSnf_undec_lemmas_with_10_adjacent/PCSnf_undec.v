Require Import Undecidability.Synthetic.Undecidability.
Require Import Undecidability.StringRewriting.PCSnf.
Require Import Undecidability.StringRewriting.SR_undec.
From Undecidability.StringRewriting.Reductions Require SR_to_PCSnf.
Check PCSnf_undec.

Lemma PCSnf_undec : undecidable PCSnf.
Proof.
apply (undecidability_from_reducibility SR_undec).
exact SR_to_PCSnf.reduction.
