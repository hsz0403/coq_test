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

Lemma If_RealiseIn R1 R2 R3 k1 k2 k3 : pM1 ⊨c(k1) R1 -> pM2 ⊨c(k2) R2 -> pM3 ⊨c(k3) R3 -> If ⊨c(1 + k1 + Nat.max k2 k3) (R1 |_true) ∘ R2 ∪ (R1 |_false) ∘ R3.
Proof.
intros.
eapply RealiseIn_monotone.
eapply Switch_RealiseIn; eauto.
-
intros.
cbn in f.
destruct f.
+
eapply RealiseIn_monotone.
destruct pM2.
eassumption.
instantiate (1 := Nat.max k2 k3); firstorder.
lia.
instantiate (1 := fun t => match t with true => R2 | _ => R3 end).
reflexivity.
+
eapply RealiseIn_monotone.
destruct pM3.
eassumption.
firstorder.
lia.
reflexivity.
-
lia.
-
hnf.
intros H2 (f& t).
intros ([ | ]& (y & H3&H3')).
left.
hnf.
eauto.
right.
hnf.
eauto.
