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

Theorem ltP_divP_pX : forall (a b : Term A n) (p q : list (Term A n)), canonical A0 eqA ltM (pX a p) -> canonical A0 eqA ltM (pX b q) -> divP A A0 eqA multA divA n a b -> ltP (A:=A) (n:=n) ltM q (pX a p).
intros a b p; case p; auto.
intros q H' H'0 H'1; try assumption.
change (ltP (A:=A) (n:=n) ltM q (pX a (pO A n))) in |- *; auto.
apply (canonical_pX_ltP A A0 eqA); apply divP_ltT_comp with (b := b); auto.
intros a0 l q H' H'0 H'1; apply ltP_trans with (y := pX a (pO A n)); auto.
apply (canonical_pX_ltP A A0 eqA); apply divP_ltT_comp with (b := b); auto.
change (ltP (A:=A) (n:=n) ltM (pX a (pO A n)) (pX a (pX a0 l))) in |- *; auto.
