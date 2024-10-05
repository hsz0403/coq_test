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

Lemma ProdCount (T1 T2: eqType) (A: list T1) (B: list T2) (a:T1) (b:T2) : count (prodLists A B) (a,b) = count A a * count B b .
Proof.
induction A.
-
reflexivity.
-
cbn.
rewrite <- countSplit.
decide (a = a0) as [E | E].
+
cbn.
f_equal.
subst a0.
apply countMap.
eauto.
+
rewrite <- plus_O_n.
f_equal.
now apply countMapZero.
Admitted.

Lemma prod_enum_ok (T1 T2: finType) (x: T1 * T2): count (prodLists (elem T1) (elem T2)) x = 1.
Proof.
destruct x as [x y].
rewrite ProdCount.
unfold elem.
Admitted.

Instance finTypeC_Prod (F1 F2: finType) : finTypeC (EqType (F1 * F2)).
Proof.
econstructor.
Admitted.

Lemma SomeElement (X: eqType) (A: list X) x: count (toOptionList A) (Some x) = count A x .
Proof.
unfold toOptionList.
simpl.
dec; try congruence.
induction A.
+
tauto.
+
simpl.
Admitted.

Lemma NoneElement (X: eqType) (A: list X) : count (toOptionList A) None = 1.
Proof.
unfold toOptionList.
simpl.
dec; try congruence.
f_equal.
induction A.
-
reflexivity.
-
Admitted.

Lemma option_enum_ok (T: finType) x : count (toOptionList (elem T)) x = 1.
Proof.
destruct x.
+
rewrite SomeElement.
apply enum_ok.
+
Admitted.

Instance finTypeC_Option(F: finType): finTypeC (EqType (option F)).
Proof.
eapply FinTypeC.
Admitted.

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
Admitted.

Instance finTypeC_sum (X Y: finType) : finTypeC (EqType ( X + Y)).
Proof.
eapply FinTypeC.
Admitted.

Lemma proveOne m n: m = 1 /\ n = 0 \/ n = 1 /\ m = 0 -> m + n = 1.
Proof.
lia.
