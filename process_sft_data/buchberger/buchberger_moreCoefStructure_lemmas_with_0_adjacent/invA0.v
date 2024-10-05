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

Theorem invA0 : eqA A0 (invA A0).
apply eqA_trans with (y := plusA A0 (invA A0)); auto.
apply eqA_trans with (y := plusA (invA A0) A0); auto.
