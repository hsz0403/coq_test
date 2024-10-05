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

Theorem divA_A1 : forall (a : A) (nZa : ~ eqA a A0), eqA (divA a a nZa) A1.
intros a nZa; apply eqA_trans with (y := divA (multA A1 a) a nZa); auto.
apply eqA_trans with (y := multA (divA A1 a nZa) a); auto.
apply divA_multA_comp_r with (1 := cs); auto.
apply eqA_sym; apply divA_is_multA with (1 := cs); auto.
