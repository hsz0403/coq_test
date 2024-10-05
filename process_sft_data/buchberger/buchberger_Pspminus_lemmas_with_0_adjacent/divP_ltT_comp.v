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

Theorem divP_ltT_comp : forall (a b : Term A n) (p : list (Term A n)), canonical A0 eqA ltM (pX b p) -> divP A A0 eqA multA divA n a b -> canonical A0 eqA ltM (pX a p).
intros a b p; case p; auto.
intros H' H'0.
change (canonical A0 eqA ltM (pX a (pO A n))) in |- *; apply canonicalp1; auto.
apply divP_inv1 with (1 := H'0); auto.
intros a0 l H' H'0; change (canonical A0 eqA ltM (pX a (pX a0 l))) in |- *; apply canonical_cons; auto.
case (ltT_dec A n ltM ltM_dec a b); [ intros tmp; case tmp; clear tmp | idtac ]; intros H'2; auto.
elim (divP_is_not_order a b); auto.
apply (ltT_trans A _ _ os) with (y := b); auto.
apply (canonical_pX_order _ A0 eqA) with (l := l); auto.
apply eqT_compat_ltTr with (b := b); auto.
apply (eqT_sym A n); auto.
apply (canonical_pX_order _ A0 eqA) with (l := l); auto.
apply divP_inv1 with (1 := H'0); auto.
apply canonical_imp_canonical with (a := b); auto.
