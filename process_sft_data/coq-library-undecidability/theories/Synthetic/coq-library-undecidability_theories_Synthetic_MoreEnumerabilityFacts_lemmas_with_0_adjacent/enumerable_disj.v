From Undecidability.Synthetic Require Import DecidabilityFacts EnumerabilityFacts ListEnumerabilityFacts.
From Undecidability.Shared Require Import ListAutomation.
Require Import List.
Import ListNotations ListAutomationNotations.

Lemma enumerable_disj X (p q : X -> Prop) : enumerable p -> enumerable q -> enumerable (fun x => p x \/ q x).
Proof.
intros [Lp H] % enumerable_enum [Lq H0] % enumerable_enum.
eapply enumerable_enum.
exists (fix f n := match n with 0 => [] | S n => f n ++ [ x | x ∈ Lp n] ++ [ y | y ∈ Lq n] end).
intros x.
split.
-
intros [H1 | H1].
*
eapply H in H1 as [m].
exists (1 + m).
cbn.
in_app 2.
in_collect x.
eauto.
*
eapply H0 in H1 as [m].
exists (1 + m).
cbn.
in_app 3.
in_collect x.
eauto.
-
intros [m].
induction m.
*
inversion H1.
*
inv_collect; unfold list_enumerator in *; firstorder.
