Require Import Undecidability.Shared.Libs.PSL.Base Lia.
Fixpoint natsLess n : list nat := match n with 0 => [] | S n => n :: natsLess n end.
Fixpoint sumn (A:list nat) := match A with [] => 0 | a::A => a + sumn A end.
Hint Rewrite sumn_app : list.
Definition maxl := fold_right max 0.

Lemma maxl_leq n l: n el l -> n <= maxl l.
Proof.
induction l;cbn.
-
easy.
-
intros [->|].
all:apply Nat.max_case_strong;try intuition Lia.lia.
