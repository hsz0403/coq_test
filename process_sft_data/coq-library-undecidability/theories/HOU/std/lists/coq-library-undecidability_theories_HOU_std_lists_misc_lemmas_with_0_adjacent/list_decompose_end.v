Set Implicit Arguments.
Require Import List Lia.
Import ListNotations.

Lemma list_decompose_end {X} (A: list X): A = nil \/ exists a' A', A = A' ++ [a'].
Proof.
induction A; intuition; subst.
all: right; try destruct IH as (a' & A' & ?).
+
exists a.
exists nil.
reflexivity.
+
destruct H as (a' & A' & ?); subst.
exists a'.
exists (a :: A').
reflexivity.
