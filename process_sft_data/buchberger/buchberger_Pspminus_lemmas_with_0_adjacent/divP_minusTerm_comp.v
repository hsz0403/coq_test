Require Export Pminus.
Require Export DivTerm.
Section Pspminus.
Load hCoefStructure.
Load hOrderStructure.
Load hMinus.
Hint Resolve divP_is_not_order : core.
Definition spminusf (a b : Term A n) (nZb : ~ zeroP (A:=A) A0 eqA (n:=n) b) (p q : list (Term A n)) := minuspf A A0 A1 eqA invA minusA multA eqA_dec n ltM ltM_dec p (mults (A:=A) multA (n:=n) (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n) a (b:=b) nZb) q).
Hint Resolve canonical_spminusf : core.
Hint Resolve canonical_spminusf_full : core.
Hint Resolve canonical_spminusf_full_t : core.
Hint Resolve spminusf_pluspf : core.
Hint Resolve eqTerm_spminusf_com eqp_spminusf_com eqp_spminusf_com : core.
Hint Resolve spminusf_plusTerm spminusf_multTerm : core.
Hint Resolve spminusf_minusTerm_r : core.
Hint Resolve spminusf_plusTerm_r : core.
Hint Resolve divP_minusTerm_comp : core.
Hint Resolve spminusf_minusTerm : core.
Hint Resolve spminusf_minusTerm : core.
End Pspminus.

Theorem divP_minusTerm_comp : forall a b c : Term A n, divP A A0 eqA multA divA n a c -> divP A A0 eqA multA divA n b c -> eqT a b -> ~ zeroP (A:=A) A0 eqA (n:=n) (minusTerm (A:=A) minusA (n:=n) a b) -> divP A A0 eqA multA divA n (minusTerm (A:=A) minusA (n:=n) a b) c.
intros a b c H' H'0 H'1 H'2.
apply divP_eqTerm_comp with (a := plusTerm (A:=A) plusA (n:=n) a (invTerm (A:=A) invA (n:=n) b)) (1 := cs); auto.
apply divP_plusTerm with (1 := cs); auto.
apply (eqT_trans A n) with (1 := H'1); auto.
apply nzeroP_comp_eqTerm with (1 := cs) (a := minusTerm (A:=A) minusA (n:=n) a b); auto.
apply (eqTerm_sym _ _ _ _ _ _ _ _ _ cs n); auto.
