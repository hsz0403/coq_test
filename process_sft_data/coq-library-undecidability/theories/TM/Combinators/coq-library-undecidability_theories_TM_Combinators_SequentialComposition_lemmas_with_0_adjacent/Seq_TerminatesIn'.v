From Undecidability.TM Require Import Util.TM_facts Switch.
Section Composition.
Variable n : nat.
Variable sig : finType.
Variable F1 : finType.
Variable pM1 : pTM sig F1 n.
Variable F2 : finType.
Variable pM2 : pTM sig F2 n.
Definition Seq := Switch pM1 (fun _ => pM2).
End Composition.
Notation "A ;; B" := (Seq A B) (right associativity, at level 65).
Arguments Seq : simpl never.

Lemma Seq_TerminatesIn' R1 T1 T2 : pM1 ⊨ R1 -> projT1 pM1 ↓ T1 -> projT1 pM2 ↓ T2 -> projT1 Seq ↓ (fun tin i => exists i1, T1 tin i1 /\ forall tout yout, R1 tin (yout, tout) -> exists i2, 1 + i1 + i2 <= i /\ T2 tout i2).
Proof.
intros HRealise HTerm1 HTerm2.
eapply TerminatesIn_monotone.
-
eapply Switch_TerminatesIn'; eauto.
instantiate (1 := fun _ => T2).
auto.
-
intros tin i (i1&HT1&H).
exists i1; repeat split; eauto.
