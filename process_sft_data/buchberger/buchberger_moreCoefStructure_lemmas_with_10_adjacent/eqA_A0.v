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

Theorem plusA_eqA_comp_l : forall a b c : A, eqA a b -> eqA (plusA a c) (plusA b c).
Admitted.

Theorem plusA_eqA_comp_r : forall a b c : A, eqA a b -> eqA (plusA c a) (plusA c b).
Admitted.

Theorem eqA0_left : forall a b : A, eqA a A0 -> eqA b (plusA a b).
intros a b H'; apply eqA_trans with (y := plusA A0 b); auto.
Admitted.

Theorem eqA0_right : forall a b : A, eqA b A0 -> eqA a (plusA a b).
Admitted.

Theorem invA0 : eqA A0 (invA A0).
apply eqA_trans with (y := plusA A0 (invA A0)); auto.
Admitted.

Theorem invA0_comp : forall a : A, eqA a A0 -> eqA a (invA a).
intros a H'; apply eqA_sym; apply eqA_trans with (y := A0); auto.
apply eqA_trans with (y := invA A0); auto.
Admitted.

Theorem invA0_inv : forall a : A, eqA a (invA (invA a)).
intros a.
apply eqA_trans with (y := plusA a A0); auto.
apply eqA_trans with (y := plusA A0 a); auto.
apply eqA_trans with (y := plusA (plusA (invA a) (invA (invA a))) a); auto.
apply eqA_trans with (y := plusA (plusA (invA (invA a)) (invA a)) a); auto.
apply eqA_trans with (y := plusA (invA (invA a)) (plusA (invA a) a)); auto.
apply eqA_trans with (y := plusA (invA (invA a)) (plusA a (invA a))); auto.
Admitted.

Theorem multA_eqA_comp_l : forall a b c : A, eqA a b -> eqA (multA a c) (multA b c).
Admitted.

Theorem multA_eqA_comp_r : forall a b c : A, eqA a b -> eqA (multA c a) (multA c b).
Admitted.

Theorem multA_dist_r : forall a b c : A, eqA (plusA (multA a c) (multA b c)) (multA (plusA a b) c).
intros a b c; apply eqA_trans with (y := plusA (multA c a) (multA c b)); auto.
Admitted.

Theorem eqA_A0 : forall a b : A, eqA a A0 -> eqA a b -> eqA b A0.
intros a b H H1; apply eqA_trans with (y := a); auto.
