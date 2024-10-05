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
simpl; dec; congruence.
