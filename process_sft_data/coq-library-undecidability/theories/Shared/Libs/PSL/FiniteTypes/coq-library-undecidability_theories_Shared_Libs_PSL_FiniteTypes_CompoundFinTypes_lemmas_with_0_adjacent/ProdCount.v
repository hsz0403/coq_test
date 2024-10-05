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
eauto.
