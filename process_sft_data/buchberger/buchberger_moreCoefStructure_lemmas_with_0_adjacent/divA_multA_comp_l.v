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

Theorem divA_multA_comp_l : forall (a b c : A) (nZc : ~ eqA c A0), eqA (divA (multA a b) c nZc) (multA a (divA b c nZc)).
intros a b c nZc; apply eqA_trans with (y := divA (multA b a) c nZc); auto.
apply eqA_trans with (y := multA (divA b c nZc) a); auto.
apply divA_multA_comp_r with (1 := cs); auto.
