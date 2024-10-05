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

Theorem A_sep : forall a b : A, eqA (multA a b) A0 -> eqA a A0 \/ eqA b A0.
intros a b H'; case (eqA_dec a A0); auto; case (eqA_dec b A0); auto.
intros nZb nZa; case nZa.
apply eqA_trans with (y := multA (divA a b nZb) b); auto.
apply divA_is_multA with (1 := cs); auto.
apply eqA_trans with (y := divA (multA a b) b nZb); auto.
apply eqA_sym; apply divA_multA_comp_r with (1 := cs); auto.
apply eqA_trans with (y := divA A0 b nZb); auto.
