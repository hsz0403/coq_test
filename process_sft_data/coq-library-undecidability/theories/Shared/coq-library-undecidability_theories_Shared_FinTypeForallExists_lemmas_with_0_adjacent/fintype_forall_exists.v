From Undecidability.Shared.Libs.PSL Require Import FiniteTypes.

Lemma fintype_forall_exists (F : finType) (P : F -> nat -> Prop) : (forall x n, P x n -> forall m, m >= n -> P x m) -> (forall x : F, exists n, P x n) -> exists N, forall x, P x N.
Proof.
intros P_mono FE.
destruct F as (X & l & Hl).
cbn in *.
destruct (@list_forall_exists X P l) as [C HC].
-
eassumption.
-
eauto.
-
exists C.
intros x.
eapply HC.
eapply count_in_equiv.
rewrite Hl.
lia.
