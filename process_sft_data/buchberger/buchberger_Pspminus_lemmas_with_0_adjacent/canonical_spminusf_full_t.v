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

Theorem canonical_spminusf_full_t : forall (a b : Term A n) (nZb : ~ zeroP (A:=A) A0 eqA (n:=n) b) (p q : list (Term A n)), canonical A0 eqA ltM (pX a p) -> canonical A0 eqA ltM (pX b q) -> divP A A0 eqA multA divA n a b -> canonical A0 eqA ltM (pX a (spminusf a b nZb p q)).
unfold spminusf in |- *.
intros a b nZb p q H' H'0 H'1; try assumption.
inversion H'1.
apply order_minuspf with (1 := cs); auto.
apply canonical_pX_eqT with (a := multTerm (A:=A) multA (n:=n) (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n) a (b:=b) nZb) b); auto.
change (canonical A0 eqA ltM (mults (A:=A) multA (n:=n) (divTerm divA a nZb) (pX b q))) in |- *; auto.
apply (eqT_sym A n); apply (eqTerm_imp_eqT A eqA n); auto.
