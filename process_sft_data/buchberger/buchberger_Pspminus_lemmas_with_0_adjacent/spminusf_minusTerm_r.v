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

Theorem spminusf_minusTerm_r : forall (a b : Term A n) (nZb : ~ zeroP (A:=A) A0 eqA (n:=n) b) (p q r : list (Term A n)), canonical A0 eqA ltM p -> canonical A0 eqA ltM q -> canonical A0 eqA ltM r -> divP A A0 eqA multA divA n a b -> eqP A eqA n (spminusf a b nZb (minuspf A A0 A1 eqA invA minusA multA eqA_dec n ltM ltM_dec p q) r) (minuspf A A0 A1 eqA invA minusA multA eqA_dec n ltM ltM_dec p (spminusf (invTerm (A:=A) invA (n:=n) a) b nZb q r)).
intros a b nZb p q r H' H'0 H'1 H'2; try assumption.
apply (eqp_trans _ _ _ _ _ _ _ _ _ cs n) with (y := spminusf a b nZb (pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec p (mults (A:=A) multA (n:=n) (invTerm (A:=A) invA (n:=n) (T1 A1 n)) q)) r); [ auto | idtac ].
apply (eqp_trans _ _ _ _ _ _ _ _ _ cs n) with (y := spminusf a b nZb (pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec (mults (A:=A) multA (n:=n) (invTerm (A:=A) invA (n:=n) (T1 A1 n)) q) p) r); [ auto | idtac ].
apply (eqp_trans _ _ _ _ _ _ _ _ _ cs n) with (y := pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec (spminusf a b nZb (mults (A:=A) multA (n:=n) (invTerm (A:=A) invA (n:=n) (T1 A1 n)) q) r) p); [ auto | idtac ].
apply (eqp_trans _ _ _ _ _ _ _ _ _ cs n) with (y := pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec p (spminusf a b nZb (mults (A:=A) multA (n:=n) (invTerm (A:=A) invA (n:=n) (T1 A1 n)) q) r)); [ auto | idtac ].
apply (eqp_sym _ _ _ _ _ _ _ _ _ cs n); apply (eqp_trans _ _ _ _ _ _ _ _ _ cs n) with (y := pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec p (mults (A:=A) multA (n:=n) (invTerm (A:=A) invA (n:=n) (T1 A1 n)) (spminusf (invTerm (A:=A) invA (n:=n) a) b nZb q r))); [ auto | idtac ].
apply eqp_pluspf_com with (1 := cs); auto.
apply (eqp_trans _ _ _ _ _ _ _ _ _ cs n) with (y := spminusf (multTerm (A:=A) multA (n:=n) (invTerm (A:=A) invA (n:=n) (T1 A1 n)) (invTerm (A:=A) invA (n:=n) a)) b nZb (mults (A:=A) multA (n:=n) (invTerm (A:=A) invA (n:=n) (T1 A1 n)) q) r); [ apply (eqp_sym _ _ _ _ _ _ _ _ _ cs n); auto | idtac ].
apply (eqp_trans _ _ _ _ _ _ _ _ _ cs n) with (y := spminusf (invTerm (A:=A) invA (n:=n) (multTerm (A:=A) multA (n:=n) (T1 A1 n) (invTerm (A:=A) invA (n:=n) a))) b nZb (mults (A:=A) multA (n:=n) (invTerm (A:=A) invA (n:=n) (T1 A1 n)) q) r); [ auto | idtac ].
apply eqTerm_spminusf_com; auto.
apply (divP_trans _ _ _ _ _ _ _ _ _ cs n) with (y := invTerm (A:=A) invA (n:=n) a); auto.
apply divTerm_multTermr with (1 := cs); auto.
apply nZero_invTerm_nZero with (1 := cs); auto.
apply divP_inv1 with (1 := H'2); auto.
apply (eqp_trans _ _ _ _ _ _ _ _ _ cs n) with (y := spminusf (invTerm (A:=A) invA (n:=n) (invTerm (A:=A) invA (n:=n) a)) b nZb (mults (A:=A) multA (n:=n) (invTerm (A:=A) invA (n:=n) (T1 A1 n)) q) r); auto.
apply eqp_spminusf_com; auto.
apply (eqTerm_sym _ _ _ _ _ _ _ _ _ cs n); auto.
apply divP_invTerm_l with (1 := cs); auto.
apply divP_eqTerm_comp with (a := invTerm (A:=A) invA (n:=n) a) (1 := cs); auto.
apply eqTerm_spminusf_com; auto.
apply (eqTerm_sym _ _ _ _ _ _ _ _ _ cs n); auto.
