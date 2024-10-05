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

Lemma Seq_Realise R1 R2 : pM1 ⊨ R1 -> pM2 ⊨ R2 -> Seq ⊨ ⋃_y ((R1 |_ y) ∘ R2).
Proof.
intros.
eapply Realise_monotone.
eapply (Switch_Realise (R1 := R1) (R2 := (fun _ => R2))); eauto.
firstorder.
