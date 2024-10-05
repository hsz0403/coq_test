From Undecidability.Shared.Libs.PSL Require Import FinTypes.
Instance finTypeC_Empty_set: finTypeC (EqType Empty_set).
Proof.
econstructor.
eapply Empty_set_enum_ok.
Defined.
Instance finTypeC_bool: finTypeC (EqType bool).
Proof.
econstructor.
apply bool_enum_ok.
Defined.
Instance finTypeC_unit: finTypeC (EqType unit).
Proof.
econstructor.
apply unit_enum_ok.
Defined.
Instance finTypeC_True : finTypeC (EqType True).
Proof.
econstructor.
apply True_enum_ok.
Defined.
Instance finTypeC_False : finTypeC (EqType False).
Proof.
econstructor.
apply False_enum_ok.
Defined.

Lemma Empty_set_enum_ok (x: Empty_set): count nil x = 1.
Proof.
tauto.
