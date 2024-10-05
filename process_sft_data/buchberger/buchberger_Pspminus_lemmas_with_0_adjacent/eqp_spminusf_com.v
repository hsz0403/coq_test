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

Theorem eqp_spminusf_com : forall (a b c : Term A n) (nZc : ~ zeroP (A:=A) A0 eqA (n:=n) c) (p q r : list (Term A n)), canonical A0 eqA ltM p -> canonical A0 eqA ltM q -> canonical A0 eqA ltM r -> eqP A eqA n p q -> eqTerm (A:=A) eqA (n:=n) a b -> divP A A0 eqA multA divA n a c -> eqP A eqA n (spminusf a c nZc p r) (spminusf b c nZc q r).
intros a b c nZc p q r H' H'0 H'1 H'2 H'3 H'4.
apply (eqp_trans _ _ _ _ _ _ _ _ _ cs n) with (y := spminusf b c nZc p r); auto.
apply eqTerm_spminusf_com; auto.
apply eqptail_spminusf_com; auto.
apply divP_eqTerm_comp with (1 := cs) (a := a); auto.
