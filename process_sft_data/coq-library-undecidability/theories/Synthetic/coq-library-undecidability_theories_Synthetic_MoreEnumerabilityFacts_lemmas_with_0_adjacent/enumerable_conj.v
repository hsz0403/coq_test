From Undecidability.Synthetic Require Import DecidabilityFacts EnumerabilityFacts ListEnumerabilityFacts.
From Undecidability.Shared Require Import ListAutomation.
Require Import List.
Import ListNotations ListAutomationNotations.

Lemma enumerable_conj X (p q : X -> Prop) : discrete X -> enumerable p -> enumerable q -> enumerable (fun x => p x /\ q x).
Proof.
intros [] % discrete_iff [Lp] % enumerable_enum [Lq] % enumerable_enum.
eapply enumerable_enum.
exists (fix f n := match n with 0 => [] | S n => f n ++ [ x | x ∈ cumul Lp n, In x (cumul Lq n)] end).
intros x.
split.
+
intros [].
eapply (list_enumerator_to_cumul H) in H1 as [m1].
eapply (list_enumerator_to_cumul H0) in H2 as [m2].
exists (1 + m1 + m2).
cbn.
in_app 2.
in_collect x.
eapply cum_ge'.
eauto.
eauto.
lia.
eapply cum_ge'; eauto.
lia.
+
intros [m].
induction m.
*
inversion H1.
*
inv_collect.
eapply (list_enumerator_to_cumul H).
eauto.
eapply (list_enumerator_to_cumul H0).
eauto.
