From Undecidability.Shared.Libs.PSL Require Import FiniteTypes.

Lemma list_forall_exists (F : Type) (P : F -> nat -> Prop) L : (forall x n, P x n -> forall m, m >= n -> P x m) -> (forall x : F, x el L -> exists n, P x n) -> exists N, forall x, x el L -> P x N.
Proof.
intros P_mono FE.
induction L.
-
exists 0.
intros ? [].
-
destruct IHL as [C HC].
+
intros; eapply FE.
eauto.
+
destruct (FE a) as [c Hc].
eauto.
exists (c + C).
intros ? [-> | ].
eapply P_mono.
eassumption.
lia.
eapply P_mono.
eapply HC.
eauto.
lia.
