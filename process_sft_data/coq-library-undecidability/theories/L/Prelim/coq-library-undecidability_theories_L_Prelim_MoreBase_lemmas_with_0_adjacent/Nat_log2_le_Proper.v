Require Export Undecidability.Shared.Libs.PSL.Base Lia.
From Undecidability.L Require Export MoreList.
Instance le_preorder : PreOrder le.
Proof.
constructor.
all:cbv.
all:intros;lia.
Instance S_le_proper : Proper (le ==> le) S.
Proof.
cbv.
fold plus.
intros.
lia.
Instance plus_le_proper : Proper (le ==> le ==> le) plus.
Proof.
cbv.
fold plus.
intros.
lia.
Instance mult_le_proper : Proper (le ==> le ==> le) mult.
Proof.
cbv.
intros.
apply mult_le_compat.
all:eauto.
Instance pow_le_proper : Proper (le ==> eq ==> le) Nat.pow.
Proof.
cbv - [Nat.pow].
intros.
subst.
apply Nat.pow_le_mono_l.
easy.
Instance max_le_proper : Proper (le ==> le ==> le) max.
Proof.
repeat intro.
repeat eapply Nat.max_case_strong;lia.
Instance min_le_proper : Proper (le ==> le ==> le) min.
Proof.
repeat intro.
repeat eapply Nat.min_case_strong;lia.
Instance Nat_log2_le_Proper : Proper (le ==> le) Nat.log2.
Proof.
repeat intro.
apply Nat.log2_le_mono.
assumption.
Instance Pos_to_nat_le_Proper : Proper (Pos.le ==> le) Pos.to_nat.
Proof.
repeat intro.
apply Pos2Nat.inj_le.
assumption.
Instance Pos_add_le_Proper : Proper (Pos.le ==> Pos.le ==>Pos.le) Pos.add.
Proof.
repeat intro.
eapply Pos.add_le_mono.
3:eauto.
all:eauto.
Definition maxP (P:nat -> Prop) m := P m /\ (forall m', P m' -> m' <= m).

Instance Nat_log2_le_Proper : Proper (le ==> le) Nat.log2.
Proof.
repeat intro.
apply Nat.log2_le_mono.
assumption.
