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

Theorem invA0_inv : forall a : A, eqA a (invA (invA a)).
intros a.
apply eqA_trans with (y := plusA a A0); auto.
apply eqA_trans with (y := plusA A0 a); auto.
apply eqA_trans with (y := plusA (plusA (invA a) (invA (invA a))) a); auto.
apply eqA_trans with (y := plusA (plusA (invA (invA a)) (invA a)) a); auto.
apply eqA_trans with (y := plusA (invA (invA a)) (plusA (invA a) a)); auto.
apply eqA_trans with (y := plusA (invA (invA a)) (plusA a (invA a))); auto.
apply eqA_trans with (y := plusA (invA (invA a)) A0); auto.
