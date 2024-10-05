Require Export CoefStructure.
Section mCoef.
Load hCoefStructure.
Load mCoefStructure.
Let eqA_trans := eqA_trans _ _ _ _ _ _ _ _ _ cs.
Let eqA_sym := eqA_sym _ _ _ _ _ _ _ _ _ cs.
Hint Resolve multA_A1_r : core.
Hint Resolve multA_invA_com_l : core.
Hint Resolve multA_invA_com_r : core.
Hint Resolve divA_multA_comp_l : core.
Hint Resolve divA_A0_l : core.
Hint Resolve A_sep : core.
Hint Resolve divA_A1 : core.
Hint Resolve divA_nZ : core.
End mCoef.

Theorem divA_nZ : forall a b : A, ~ eqA b A0 -> forall nZa : ~ eqA a A0, ~ eqA (divA b a nZa) A0.
intros a b H' nZa; red in |- *; intros H'1; auto.
case H'; apply eqA_trans with (y := multA (divA b a nZa) a); auto.
apply divA_is_multA with (1 := cs); auto.
apply eqA_trans with (y := multA A0 a); auto.
