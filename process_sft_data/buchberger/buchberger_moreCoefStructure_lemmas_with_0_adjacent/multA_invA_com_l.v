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

Theorem multA_invA_com_l : forall a b : A, eqA (multA (invA a) b) (invA (multA a b)).
intros a b; apply eqA_trans with (y := plusA (invA (multA a b)) A0); auto.
apply eqA_trans with (y := plusA A0 (invA (multA a b))); auto.
apply eqA_trans with (y := plusA (multA A0 b) (invA (multA a b))); auto.
apply eqA_trans with (y := plusA (multA (plusA a (invA a)) b) (invA (multA a b))); auto.
apply eqA_trans with (y := plusA (plusA (multA a b) (multA (invA a) b)) (invA (multA a b))); auto.
apply eqA_trans with (y := plusA (plusA (multA (invA a) b) (multA a b)) (invA (multA a b))); auto.
apply eqA_trans with (y := plusA (multA (invA a) b) (plusA (multA a b) (invA (multA a b)))); auto.
apply eqA_trans with (y := plusA (multA (invA a) b) A0); auto.
apply plusA_eqA_comp with (1 := cs); auto.
apply multA_dist_r.
