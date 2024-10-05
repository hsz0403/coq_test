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

Theorem spminusf_minusTerm : forall (a b c : Term A n) (nZc : ~ zeroP (A:=A) A0 eqA (n:=n) c) (p q r : list (Term A n)), canonical A0 eqA ltM p -> canonical A0 eqA ltM q -> canonical A0 eqA ltM r -> divP A A0 eqA multA divA n a c -> divP A A0 eqA multA divA n b c -> eqT a b -> ~ zeroP (A:=A) A0 eqA (n:=n) (minusTerm (A:=A) minusA (n:=n) a b) -> eqP A eqA n (spminusf (minusTerm (A:=A) minusA (n:=n) a b) c nZc (minuspf A A0 A1 eqA invA minusA multA eqA_dec n ltM ltM_dec p q) r) (minuspf A A0 A1 eqA invA minusA multA eqA_dec n ltM ltM_dec (spminusf a c nZc p r) (spminusf b c nZc q r)).
intros a b c nZc p q r H' H'0 H'1 H'2 H'3 H'4 H'5.
apply (eqp_trans _ _ _ _ _ _ _ _ _ cs n) with (y := spminusf (plusTerm (A:=A) plusA (n:=n) a (invTerm (A:=A) invA (n:=n) b)) c nZc (minuspf A A0 A1 eqA invA minusA multA eqA_dec n ltM ltM_dec p q) r); [ auto | idtac ].
apply (eqp_trans _ _ _ _ _ _ _ _ _ cs n) with (y := spminusf (plusTerm (A:=A) plusA (n:=n) a (invTerm (A:=A) invA (n:=n) b)) c nZc (pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec p (mults (A:=A) multA (n:=n) (invTerm (A:=A) invA (n:=n) (T1 A1 n)) q)) r); [ auto | idtac ].
apply eqp_spminusf_com; auto.
apply divP_eqTerm_comp with (a := minusTerm (A:=A) minusA (n:=n) a b) (1 := cs); auto.
apply (eqp_trans _ _ _ _ _ _ _ _ _ cs n) with (y := pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec (spminusf a c nZc p r) (spminusf (invTerm (A:=A) invA (n:=n) b) c nZc (mults (A:=A) multA (n:=n) (invTerm (A:=A) invA (n:=n) (T1 A1 n)) q) r)); [ auto | idtac ].
apply spminusf_plusTerm; auto.
apply (eqT_trans A n) with (1 := H'4); auto.
apply nzeroP_comp_eqTerm with (1 := cs) (a := minusTerm (A:=A) minusA (n:=n) a b); auto.
apply (eqp_sym _ _ _ _ _ _ _ _ _ cs n); apply (eqp_trans _ _ _ _ _ _ _ _ _ cs n) with (y := pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec (spminusf a c nZc p r) (mults (A:=A) multA (n:=n) (invTerm (A:=A) invA (n:=n) (T1 A1 n)) (spminusf b c nZc q r))); [ auto | idtac ].
apply eqp_pluspf_com with (1 := cs); auto.
apply (eqp_trans _ _ _ _ _ _ _ _ _ cs n) with (y := spminusf (multTerm (A:=A) multA (n:=n) (invTerm (A:=A) invA (n:=n) (T1 A1 n)) b) c nZc (mults (A:=A) multA (n:=n) (invTerm (A:=A) invA (n:=n) (T1 A1 n)) q) r); [ auto | idtac ].
apply (eqp_sym _ _ _ _ _ _ _ _ _ cs n); auto.
apply (eqp_trans _ _ _ _ _ _ _ _ _ cs n) with (y := spminusf (invTerm (A:=A) invA (n:=n) (multTerm (A:=A) multA (n:=n) (T1 A1 n) b)) c nZc (mults (A:=A) multA (n:=n) (invTerm (A:=A) invA (n:=n) (T1 A1 n)) q) r); [ auto | auto ].
apply eqTerm_spminusf_com; auto.
apply (divP_trans _ _ _ _ _ _ _ _ _ cs n) with (y := b); auto.
apply divTerm_multTermr with (1 := cs); auto.
inversion H'3; auto.
apply eqTerm_spminusf_com; auto.
apply (eqTerm_sym _ _ _ _ _ _ _ _ _ cs n); auto.
apply (divP_trans _ _ _ _ _ _ _ _ _ cs n) with (y := b); auto.
inversion H'3; auto.
