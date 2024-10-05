Require Import Undecidability.TM.SBTM.
Require Import Undecidability.Synthetic.Definitions.
Require Import Equations.Equations.
Section fixM.
Variable M : SBTM.
Definition M' : SBTM.
Proof.
exists (1 + num_states M).
intros [q o].
dependent elimination q.
-
destruct (trans M (Fin.F1, o)) as [[[q' w] m] | ].
dependent elimination q'.
+
exact (Some (Fin.F1, w, m)).
+
exact (Some (Fin.FS (Fin.FS t), w, m)).
+
exact (Some (Fin.FS Fin.F1, None, Nmove)).
-
dependent elimination t.
+
exact None.
+
destruct (trans M (Fin.FS t, o)) as [[[q' w] m] | ].
dependent elimination q'.
*
exact (Some (Fin.F1, w, m)).
*
exact (Some (Fin.FS (Fin.FS t0), w, m)).
*
exact (Some (Fin.FS Fin.F1, None, Nmove)).
Defined.
Definition conv_state (q : Fin.t (S (num_states M))) : Fin.t (S (1 + num_states M)).
Proof.
dependent elimination q.
exact Fin.F1.
exact (Fin.FS (Fin.FS t)).
Defined.
End fixM.

Lemma spec2 c q' : trans M' (q', c) = None -> q' = Fin.FS Fin.F1.
Proof.
cbn.
dependent elimination q'.
-
cbn.
destruct (trans M (Fin.F1, c)) as [[[q' w] m] | ].
dependent elimination q'; cbn; congruence.
inversion 1.
-
cbn.
dependent elimination t; cbn.
+
reflexivity.
+
destruct (trans M) as [[[q' w] m] | ].
dependent elimination q'; cbn; congruence.
inversion 1.
