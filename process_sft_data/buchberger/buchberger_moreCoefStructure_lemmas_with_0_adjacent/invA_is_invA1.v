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

Theorem invA_is_invA1 : forall a : A, eqA (invA a) (multA (invA A1) a).
intros a; apply eqA_trans with (y := plusA (invA a) A0); auto.
apply eqA_trans with (y := plusA (invA a) (multA A0 a)); auto.
apply eqA_trans with (y := plusA (invA a) (multA (plusA A1 (invA A1)) a)); auto.
apply eqA_trans with (y := plusA (invA a) (plusA (multA A1 a) (multA (invA A1) a))); auto.
apply plusA_eqA_comp with (1 := cs); auto.
apply eqA_sym; auto.
apply multA_dist_r.
apply eqA_trans with (y := plusA (invA a) (plusA a (multA (invA A1) a))); auto.
apply eqA_trans with (y := plusA (plusA (invA a) a) (multA (invA A1) a)); auto.
apply eqA_trans with (y := plusA (plusA a (invA a)) (multA (invA A1) a)); auto.
apply eqA_trans with (y := plusA A0 (multA (invA A1) a)); auto.
apply eqA_trans with (y := plusA (multA (invA A1) a) A0); auto.
