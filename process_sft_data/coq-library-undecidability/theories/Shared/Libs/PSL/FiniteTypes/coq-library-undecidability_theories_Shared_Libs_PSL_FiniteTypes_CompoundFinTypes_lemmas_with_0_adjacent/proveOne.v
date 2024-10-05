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

Lemma proveOne m n: m = 1 /\ n = 0 \/ n = 1 /\ m = 0 -> m + n = 1.
Proof.
lia.
