Require Import Undecidability.Shared.Libs.PSL.Base Lia.
Fixpoint natsLess n : list nat := match n with 0 => [] | S n => n :: natsLess n end.
Fixpoint sumn (A:list nat) := match A with [] => 0 | a::A => a + sumn A end.
Hint Rewrite sumn_app : list.
Definition maxl := fold_right max 0.

Lemma maxl_leq_l c l : (forall n, n el l -> n <= c) -> maxl l <= c.
Proof.
induction l;cbn.
Lia.lia.
intros H.
eapply Nat.max_lub_iff;split.
all:eauto.
