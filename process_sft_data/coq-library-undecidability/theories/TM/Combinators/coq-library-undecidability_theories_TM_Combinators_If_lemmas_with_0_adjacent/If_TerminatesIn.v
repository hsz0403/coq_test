From Undecidability.TM Require Import Util.TM_facts Switch.
Section If.
Variable n : nat.
Variable sig : finType.
Variable pM1 : pTM sig bool n.
Variable F : finType.
Variable pM2 : pTM sig F n.
Variable pM3 : pTM sig F n.
Definition If := Switch pM1 (fun b => if b then pM2 else pM3).
End If.
Arguments If : simpl never.

Lemma If_TerminatesIn R1 T1 T2 T3 : pM1 ⊨ R1 -> projT1 pM1 ↓ T1 -> projT1 pM2 ↓ T2 -> projT1 pM3 ↓ T3 -> projT1 If ↓ (fun tin i => exists i1 i2, T1 tin i1 /\ 1 + i1 + i2 <= i /\ forall tout (b:bool), R1 tin (b, tout) -> if b then T2 tout i2 else T3 tout i2).
Proof.
intros HRelalise HTerm1 HTerm2 HTerm3.
eapply TerminatesIn_monotone.
-
eapply Switch_TerminatesIn; cbn; eauto.
instantiate (1 := fun f => if f then T2 else T3).
intros [ | ]; cbn; auto.
-
intros tin k (i1&i2&Hi&HT1&HT2).
exists i1, i2.
repeat split; eauto.
intros tout b HRel.
specialize (HT2 tout b HRel).
destruct b; auto.
