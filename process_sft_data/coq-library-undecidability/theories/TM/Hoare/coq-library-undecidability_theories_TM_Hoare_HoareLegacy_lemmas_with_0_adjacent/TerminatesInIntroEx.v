From Undecidability.TM Require Import TM Util.TM_facts HoareLogic HoareRegister.

Lemma TerminatesInIntroEx sig n X (T : forall _ _ _, Prop) (M : TM sig n): (forall x, M ↓ (fun tin k => T x tin k)) -> M ↓ (fun tin k => exists (x:X), T x tin k).
Proof.
unfold TerminatesIn.
intros.
firstorder.
