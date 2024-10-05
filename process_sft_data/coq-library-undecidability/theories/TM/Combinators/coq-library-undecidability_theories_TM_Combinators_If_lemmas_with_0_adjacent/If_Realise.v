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

Lemma If_Realise R1 R2 R3 : pM1 ⊨ R1 -> pM2 ⊨ R2 -> pM3 ⊨ R3 -> If ⊨ (R1 |_true) ∘ R2 ∪ (R1 |_false) ∘ R3.
Proof.
intros.
eapply Realise_monotone.
-
eapply (Switch_Realise (R1 := R1) (R2 := (fun b => if b then R2 else R3))); eauto.
now intros [].
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
