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

Theorem divP_is_not_order : forall a b : Term A n, divP A A0 eqA multA divA n a b -> ~ ltT ltM a b.
intros a b H'; inversion H'.
case (ltT_dec A n ltM ltM_dec (T1 A1 n) (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n) a (b:=b) nZb)); [ intros tmp; case tmp; clear tmp | idtac ]; intros H'2; auto.
apply ltT_not_ltT; auto.
apply ltT_eqTl with (a := multTerm (A:=A) multA (n:=n) (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n) a (b:=b) nZb) b); auto.
apply (eqT_sym A n); apply (eqTerm_imp_eqT A eqA); auto.
apply ltT_eqTr with (a := multTerm (A:=A) multA (n:=n) (T1 A1 n) b); auto.
apply (eqT_sym A n); apply (eqTerm_imp_eqT A eqA); apply T1_multTerm_l with (1 := cs); auto.
apply multTerm_ltT_r with (1 := os); auto.
elim (T1_is_min_ltT A A1) with (a := divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n) a (b:=b) nZb) (1 := os); auto.
apply ltT_not_eqT; auto.
apply (eqT_trans A n) with (y := multTerm (A:=A) multA (n:=n) (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n) a (b:=b) nZb) b); auto.
apply (eqTerm_imp_eqT A eqA); auto.
apply (eqT_trans A n) with (y := multTerm (A:=A) multA (n:=n) (T1 A1 n) b); auto.
apply (eqT_sym A n); auto.
apply (eqT_sym A n); apply (eqTerm_imp_eqT A eqA); auto.
