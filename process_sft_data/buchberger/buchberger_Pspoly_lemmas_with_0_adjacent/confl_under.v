Require Export Preducestar.
Require Export LetP.
Section Pspoly.
Load hCoefStructure.
Load hOrderStructure.
Load hReducestar.
Definition spolyf : forall (p q : list (Term A n)) (Cp : canonical A0 eqA ltM p) (Cq : canonical A0 eqA ltM q), list (Term A n).
intros p1; case p1.
intros p2 H' H'0; exact (pO A n).
intros a p11 p2; case p2.
intros H' H'0; exact (pO A n).
intros b p22 H' H'0.
apply LetP with (A := Term A n) (h := ppc (A:=A) A1 (n:=n) a b).
intros u H'1.
cut (~ zeroP (A:=A) A0 eqA (n:=n) a); [ intros nZa | apply canonical_nzeroP with (ltM := ltM) (p := p11); auto ].
cut (~ zeroP (A:=A) A0 eqA (n:=n) b); [ intros nZb | apply canonical_nzeroP with (ltM := ltM) (p := p22); auto ].
exact (minuspf A A0 A1 eqA invA minusA multA eqA_dec n ltM ltM_dec (mults (A:=A) multA (n:=n) (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n) u (b:=a) nZa) p11) (mults (A:=A) multA (n:=n) (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n) u (b:=b) nZb) p22)).
Defined.
Hint Resolve spolyf_canonical : core.
Hint Resolve spolyf_def : core.
Inductive ReduStarConfluent (Q : list (poly A0 eqA ltM)) (p : list (Term A n)) : Prop := ReduStarConfluent0 : (forall r s : list (Term A n), reducestar A A0 A1 eqA invA minusA multA divA eqA_dec n ltM ltM_dec Q p r -> reducestar A A0 A1 eqA invA minusA multA divA eqA_dec n ltM ltM_dec Q p s -> eqP A eqA n r s) -> ReduStarConfluent Q p.
Inductive Spoly_1 (Q : list (poly A0 eqA ltM)) : list (Term A n) -> list (Term A n) -> Prop := | Spoly_10 : forall (p q : list (Term A n)) (Cp : canonical A0 eqA ltM p) (Cq : canonical A0 eqA ltM q), reducestar A A0 A1 eqA invA minusA multA divA eqA_dec n ltM ltM_dec Q (spolyf p q Cp Cq) (pO A n) -> Spoly_1 Q p q | Spoly_11 : forall (b c d : Term A n) (q r r0 s0 t : list (Term A n)), Spoly_1 Q (pX c r) (pX d t) -> Spoly_1 Q (pX d t) (pX b q) -> inPolySet A A0 eqA n ltM (pX d t) Q -> divP A A0 eqA multA divA n (ppc (A:=A) A1 (n:=n) c b) d -> Spoly_1 Q (pX c r) (pX b q).
Inductive SpolyQ (Q : list (poly A0 eqA ltM)) : Prop := SpolyQ0 : (forall p q : list (Term A n), inPolySet A A0 eqA n ltM p Q -> canonical A0 eqA ltM p -> inPolySet A A0 eqA n ltM q Q -> canonical A0 eqA ltM q -> Spoly_1 Q p q) -> SpolyQ Q.
Inductive Reducep (Q : list (poly A0 eqA ltM)) : list (Term A n) -> list (Term A n) -> list (Term A n) -> Prop := Reducep0 : forall (a b c : Term A n) (nZb : ~ zeroP (A:=A) A0 eqA (n:=n) b) (nZc : ~ zeroP (A:=A) A0 eqA (n:=n) c) (p q r : list (Term A n)), reduce A A0 A1 eqA invA minusA multA divA eqA_dec n ltM ltM_dec Q (pX a p) (spminusf A A0 A1 eqA invA minusA multA divA eqA_dec n ltM ltM_dec a b nZb p q) -> reduce A A0 A1 eqA invA minusA multA divA eqA_dec n ltM ltM_dec Q (pX a p) (spminusf A A0 A1 eqA invA minusA multA divA eqA_dec n ltM ltM_dec a c nZc p r) -> divP A A0 eqA multA divA n a b -> inPolySet A A0 eqA n ltM (pX b q) Q -> divP A A0 eqA multA divA n a c -> inPolySet A A0 eqA n ltM (pX c r) Q -> Reducep Q (pX a p) (pX b q) (pX c r).
Inductive Confluent (Q : list (poly A0 eqA ltM)) : list (Term A n) -> list (Term A n) -> list (Term A n) -> Prop := Confluent0 : forall (a b c : Term A n) (nZb : ~ zeroP (A:=A) A0 eqA (n:=n) b) (nZc : ~ zeroP (A:=A) A0 eqA (n:=n) c) (p q r : list (Term A n)), (forall r1 s1 : list (Term A n), reducestar A A0 A1 eqA invA minusA multA divA eqA_dec n ltM ltM_dec Q (spminusf A A0 A1 eqA invA minusA multA divA eqA_dec n ltM ltM_dec a b nZb p q) r1 -> reducestar A A0 A1 eqA invA minusA multA divA eqA_dec n ltM ltM_dec Q (spminusf A A0 A1 eqA invA minusA multA divA eqA_dec n ltM ltM_dec a c nZc p r) s1 -> eqP A eqA n r1 s1) -> Confluent Q (pX a p) (pX b q) (pX c r).
Hint Resolve pO_irreducible : core.
End Pspoly.

Theorem confl_under : forall (Q : list (poly A0 eqA ltM)) (a : Term A n) (p : list (Term A n)), canonical A0 eqA ltM (pX a p) -> (forall q : list (Term A n), canonical A0 eqA ltM q -> ltP (A:=A) (n:=n) ltM q (pX a p) -> ReduStarConfluent Q q) -> forall r s : list (Term A n), reduce A A0 A1 eqA invA minusA multA divA eqA_dec n ltM ltM_dec Q (pX a p) (pX a r) -> reduce A A0 A1 eqA invA minusA multA divA eqA_dec n ltM ltM_dec Q (pX a p) (pX a s) -> forall r1 s1 : list (Term A n), reducestar A A0 A1 eqA invA minusA multA divA eqA_dec n ltM ltM_dec Q (pX a r) r1 -> reducestar A A0 A1 eqA invA minusA multA divA eqA_dec n ltM ltM_dec Q (pX a s) s1 -> eqP A eqA n r1 s1.
intros Q a p Op1 H'0 r s H'1 H'2 r1 s1 H'3 H'4.
cut (canonical A0 eqA ltM p); [ intros Op2 | apply canonical_imp_canonical with (a := a); auto ].
cut (canonical A0 eqA ltM (pX a r)); [ intros Op3 | apply canonical_reduce with (1 := cs) (3 := H'1); auto ].
cut (canonical A0 eqA ltM r); [ intros Op4 | apply canonical_imp_canonical with (a := a); auto ].
cut (canonical A0 eqA ltM (pX a s)); [ intros Op5 | apply canonical_reduce with (1 := cs) (3 := H'2); auto ].
cut (canonical A0 eqA ltM s); [ intros Op6 | apply canonical_imp_canonical with (a := a); auto ].
lapply (H'0 p); [ intros H'5; lapply H'5; [ intros H'6; elim H'6; clear H'5 | apply ltP_refl_pX with (1 := cs) ] | idtac ]; auto.
intros H'5.
elim reduce0_reducestar with (1 := cs) (eqA_dec := eqA_dec) (ltM_dec := ltM_dec) (Q := Q) (p := s); auto; intros s0 E.
elim reduce0_reducestar with (1 := cs) (eqA_dec := eqA_dec) (ltM_dec := ltM_dec) (Q := Q) (p := r); auto; intros r0 E0.
cut (reduceplus A A0 A1 eqA invA minusA multA divA eqA_dec n ltM ltM_dec Q (pX a r) (pX a r0)); [ intros red1 | apply reduceplus_skip with (1 := cs); auto; elim E0 ]; auto.
cut (canonical A0 eqA ltM (pX a r0)); [ intros Op7 | apply canonical_reduceplus with (1 := cs) (3 := red1) ]; auto.
cut (reduceplus A A0 A1 eqA invA minusA multA divA eqA_dec n ltM ltM_dec Q (pX a s) (pX a s0)); [ intros red2 | apply reduceplus_skip with (1 := cs); auto; elim E ]; auto.
cut (canonical A0 eqA ltM (pX a s0)); [ intros Op8 | apply canonical_reduceplus with (1 := cs) (3 := red2) ]; auto.
cut (eqP A eqA n (pX a r0) (pX a s0)); [ intros eqPR1 | auto ].
elim reduce0_reducestar with (1 := cs) (eqA_dec := eqA_dec) (ltM_dec := ltM_dec) (Q := Q) (p := pX a r0); auto; intros t0 E1.
elim reduce0_reducestar with (1 := cs) (eqA_dec := eqA_dec) (ltM_dec := ltM_dec) (Q := Q) (p := pX a s0); auto; intros t1 E2.
cut (reducestar A A0 A1 eqA invA minusA multA divA eqA_dec n ltM ltM_dec Q (pX a r) t0); [ intros red3 | apply (reducestar_trans A A0 A1 eqA plusA invA minusA multA divA cs eqA_dec n ltM ltM_dec os Q) with (y := pX a r0) ]; auto.
cut (reducestar A A0 A1 eqA invA minusA multA divA eqA_dec n ltM ltM_dec Q (pX a s) t1); [ intros red4 | apply (reducestar_trans A A0 A1 eqA plusA invA minusA multA divA cs eqA_dec n ltM ltM_dec os Q) with (y := pX a s0) ]; auto.
cut (eqP A eqA n t0 t1); [ intros eqPR2 | auto ].
apply (eqp_trans _ _ _ _ _ _ _ _ _ cs n) with (y := t0); auto.
lapply (H'0 (pX a r)); [ intros H'7; lapply H'7; [ intros H'8; elim H'8; clear H'7 | clear H'7 ] | idtac ]; auto.
apply ltP_reduce with (1 := cs) (3 := H'1); auto.
apply (eqp_trans _ _ _ _ _ _ _ _ _ cs n) with (y := t1); auto.
lapply (H'0 (pX a s)); [ intros H'7; lapply H'7; [ intros H'8; elim H'8; clear H'7 | clear H'7 ] | idtac ]; auto.
apply ltP_reduce with (1 := cs) (3 := H'2); auto.
lapply (reducestar_eqp_com _ _ _ _ _ _ _ _ _ cs eqA_dec n ltM ltM_dec os Q (pX a r0) t0 (pX a s0) t0); [ intros H'11; lapply H'11; [ intros H'12; lapply H'12; [ intros H'13; lapply H'13; [ intros H'14; clear H'13 H'12 H'11 | clear H'13 H'12 H'11 ] | clear H'12 H'11 ] | clear H'11 ] | idtac ]; auto.
lapply (H'0 (pX a s0)); [ intros H'7; lapply H'7; [ intros H'8; elim H'8; clear H'7 | clear H'7 ] | idtac ]; auto.
elim order_reduceplus with (1 := cs) (Q := Q) (p := pX a s) (q := pX a s0) (ltM_dec := ltM_dec) (eqA_dec := eqA_dec); auto.
intros H'13; apply ltP_trans with (y := pX a s); auto.
apply ltP_reduce with (1 := cs) (ltM_dec := ltM_dec) (eqA_dec := eqA_dec) (Q := Q); auto.
intros H'13; apply (ltp_eqp_comp A A0 eqA) with (ltM := ltM) (p := pX a s) (q := pX a p); auto.
apply ltP_reduce with (Q := Q) (1 := cs) (ltM_dec := ltM_dec) (eqA_dec := eqA_dec); auto.
apply eqpP1; auto.
apply H'5; auto.
inversion_clear E0; auto.
apply reducestar0; auto.
apply Rstar_n with (y := r); auto.
apply reduce_inv with (1 := cs) (3 := H'1); auto.
apply reducestar0; auto.
apply Rstar_n with (y := s); auto.
apply reduce_inv with (1 := cs) (3 := H'2); auto.
inversion_clear E; auto.
inversion_clear E; auto.
