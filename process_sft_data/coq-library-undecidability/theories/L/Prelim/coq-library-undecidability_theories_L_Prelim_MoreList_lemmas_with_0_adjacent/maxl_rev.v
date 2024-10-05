Require Import Undecidability.Shared.Libs.PSL.Base Lia.
Fixpoint natsLess n : list nat := match n with 0 => [] | S n => n :: natsLess n end.
Fixpoint sumn (A:list nat) := match A with [] => 0 | a::A => a + sumn A end.
Hint Rewrite sumn_app : list.
Definition maxl := fold_right max 0.

Lemma maxl_rev l: maxl (rev l) = maxl l.
Proof.
unfold maxl.
rewrite fold_left_rev_right.
rewrite fold_symmetric.
2,3:now intros;Lia.lia.
induction l;cbn;try Lia.lia.
