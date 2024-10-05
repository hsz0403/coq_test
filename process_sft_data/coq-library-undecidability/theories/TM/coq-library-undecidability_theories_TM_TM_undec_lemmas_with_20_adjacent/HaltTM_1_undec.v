Require Import Undecidability.Synthetic.Undecidability.
Require Import Undecidability.TM.TM.
Require Import Undecidability.TM.Reductions.mTM_to_TM.

Lemma HaltMTM_undec : undecidable HaltMTM.
Proof.
apply (undecidability_from_reducibility HaltTM_1_undec).
Admitted.

Lemma HaltTM_1_undec : undecidable (HaltTM 1).
Proof.
intros d.
exact d.
