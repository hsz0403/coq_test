From Undecidability.TM Require Import Single.StepTM Code.CodeTM TM.
Require Import Undecidability.Synthetic.Definitions.

Lemma nTM_to_MTM n : HaltTM n ⪯ HaltMTM.
Proof.
unshelve eexists.
-
intros [Sig M t].
exists (n, Sig); eassumption.
-
intros [Sig M t].
cbn.
firstorder.
