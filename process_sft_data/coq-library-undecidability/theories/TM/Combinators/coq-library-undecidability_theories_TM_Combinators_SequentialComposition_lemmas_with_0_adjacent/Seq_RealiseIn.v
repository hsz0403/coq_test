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

Lemma Seq_RealiseIn (R1 : Rel _ _) (R2 : Rel _ (F2 * _)) k1 k2: pM1 ⊨c(k1) R1 -> pM2 ⊨c(k2) R2 -> Seq ⊨c(1 + k1 + k2) ⋃_y ((R1 |_y) ∘ R2).
Proof.
intros H1 H2.
eapply RealiseIn_monotone.
eapply (Switch_RealiseIn).
-
eapply H1.
-
intros f.
eapply H2.
-
lia.
-
firstorder.
