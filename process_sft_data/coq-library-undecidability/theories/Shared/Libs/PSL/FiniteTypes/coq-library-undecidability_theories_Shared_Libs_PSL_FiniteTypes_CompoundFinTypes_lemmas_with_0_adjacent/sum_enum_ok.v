From Undecidability.Shared.Libs.PSL Require Import FinTypes.
Instance finTypeC_Prod (F1 F2: finType) : finTypeC (EqType (F1 * F2)).
Proof.
econstructor.
apply prod_enum_ok.
Defined.
Instance finTypeC_Option(F: finType): finTypeC (EqType (option F)).
Proof.
eapply FinTypeC.
apply option_enum_ok.
Defined.
Instance finTypeC_sum (X Y: finType) : finTypeC (EqType ( X + Y)).
Proof.
eapply FinTypeC.
apply sum_enum_ok.
Defined.
Hint Extern 4 (finTypeC (EqType (_ * _))) => eapply finTypeC_Prod : typeclass_instances.
Hint Extern 4 (finTypeC (EqType (_ + _))) => eapply finTypeC_sum : typeclass_instances.
Hint Extern 4 (finTypeC (EqType (option _))) => eapply finTypeC_Option : typeclass_instances.

Lemma sum_enum_ok (X: finType) (Y: finType) x : count (toSumList1 Y (elem X) ++ toSumList2 X (elem Y)) x = 1.
Proof.
rewrite <- countSplit.
apply proveOne.
destruct x.
-
left.
split; cbn.
+
rewrite toSumList1_count.
apply enum_ok.
+
apply toSumList2_missing.
-
right.
split; cbn.
+
rewrite toSumList2_count.
apply enum_ok.
+
apply toSumList1_missing.
