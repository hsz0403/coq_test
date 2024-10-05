Require Import Undecidability.Shared.Libs.PSL.Base Lia.
Fixpoint natsLess n : list nat := match n with 0 => [] | S n => n :: natsLess n end.
Fixpoint sumn (A:list nat) := match A with [] => 0 | a::A => a + sumn A end.
Hint Rewrite sumn_app : list.
Definition maxl := fold_right max 0.

Lemma natsLess_in_iff n m: n el natsLess m <-> n < m.
Proof.
induction m in n|-*;cbn.
lia.
split.
-
intuition.
destruct n;intuition.
apply IHm in H0.
lia.
-
intros.
decide (m=n).
intuition.
right.
apply IHm.
lia.
