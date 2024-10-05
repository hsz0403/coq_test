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

Theorem spolyf_canonical : forall (p q : list (Term A n)) (Cp : canonical A0 eqA ltM p) (Cq : canonical A0 eqA ltM q), canonical A0 eqA ltM (spolyf p q Cp Cq).
intros p; case p; simpl in |- *; auto.
intros a l q; case q; unfold LetP in |- *; simpl in |- *; auto.
intros a0 l0 H' H'0.
cut (canonical A0 eqA ltM l0); [ intros Op1 | apply canonical_imp_canonical with (a := a0) ]; auto.
cut (canonical A0 eqA ltM l); [ intros Op2 | apply canonical_imp_canonical with (a := a) ]; auto.
cut (~ zeroP (A:=A) A0 eqA (n:=n) a); [ intros Z0 | apply canonical_nzeroP with (ltM := ltM) (p := l); auto ].
Admitted.

Theorem spolyf_pO : forall (a : list (Term A n)) (Ca : canonical A0 eqA ltM a), eqP A eqA n (spolyf a a Ca Ca) (pO A n).
intros a; case a; simpl in |- *; unfold LetP in |- *; auto.
Admitted.

Theorem spolyf_com : forall (a b : list (Term A n)) (Ca : canonical A0 eqA ltM a) (Cb : canonical A0 eqA ltM b), eqP A eqA n (spolyf a b Ca Cb) (mults (A:=A) multA (n:=n) (invTerm (A:=A) invA (n:=n) (T1 A1 n)) (spolyf b a Cb Ca)).
intros a b; case a; case b; simpl in |- *; auto.
intros a0 l a1 l0 Cpxa0 Cpxa1.
cut (~ zeroP (A:=A) A0 eqA (n:=n) a0); [ intros nZa0 | apply canonical_nzeroP with (ltM := ltM) (p := l); auto ].
cut (~ zeroP (A:=A) A0 eqA (n:=n) a1); [ intros nZa1 | apply canonical_nzeroP with (ltM := ltM) (p := l0); auto ].
change (eqP A eqA n (minuspf A A0 A1 eqA invA minusA multA eqA_dec n ltM ltM_dec (mults (A:=A) multA (n:=n) (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n) (ppc (A:=A) A1 (n:=n) a1 a0) (b:=a1) (canonical_nzeroP A A0 eqA n ltM a1 l0 Cpxa0)) l0) (mults (A:=A) multA (n:=n) (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n) (ppc (A:=A) A1 (n:=n) a1 a0) (b:=a0) (canonical_nzeroP A A0 eqA n ltM a0 l Cpxa1)) l)) (mults (A:=A) multA (n:=n) (invTerm (A:=A) invA (n:=n) (T1 A1 n)) (minuspf A A0 A1 eqA invA minusA multA eqA_dec n ltM ltM_dec (mults (A:=A) multA (n:=n) (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n) (ppc (A:=A) A1 (n:=n) a0 a1) (b:=a0) (canonical_nzeroP A A0 eqA n ltM a0 l Cpxa1)) l) (mults (A:=A) multA (n:=n) (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n) (ppc (A:=A) A1 (n:=n) a0 a1) (b:=a1) (canonical_nzeroP A A0 eqA n ltM a1 l0 Cpxa0)) l0)))) in |- *.
cut (canonical A0 eqA ltM l); [ intros Op1 | apply canonical_imp_canonical with (a := a0); auto ].
cut (canonical A0 eqA ltM l0); [ intros Op2 | apply canonical_imp_canonical with (a := a1); auto ].
apply (eqp_trans _ _ _ _ _ _ _ _ _ cs n) with (y := pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec (mults (A:=A) multA (n:=n) (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n) (ppc (A:=A) A1 (n:=n) a1 a0) (b:=a1) (canonical_nzeroP A A0 eqA n ltM a1 l0 Cpxa0)) l0) (mults (A:=A) multA (n:=n) (invTerm (A:=A) invA (n:=n) (T1 A1 n)) (mults (A:=A) multA (n:=n) (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n) (ppc (A:=A) A1 (n:=n) a1 a0) (b:=a0) (canonical_nzeroP A A0 eqA n ltM a0 l Cpxa1)) l))); [ auto | idtac ].
apply (eqp_trans _ _ _ _ _ _ _ _ _ cs n) with (y := pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec (mults (A:=A) multA (n:=n) (T1 A1 n) (mults (A:=A) multA (n:=n) (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n) (ppc (A:=A) A1 (n:=n) a1 a0) (b:=a1) (canonical_nzeroP A A0 eqA n ltM a1 l0 Cpxa0)) l0)) (mults (A:=A) multA (n:=n) (invTerm (A:=A) invA (n:=n) (T1 A1 n)) (mults (A:=A) multA (n:=n) (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n) (ppc (A:=A) A1 (n:=n) a1 a0) (b:=a0) (canonical_nzeroP A A0 eqA n ltM a0 l Cpxa1)) l))).
apply (eqp_sym _ _ _ _ _ _ _ _ _ cs n); apply eqp_pluspf_com with (1 := cs); auto.
apply (eqp_trans _ _ _ _ _ _ _ _ _ cs n) with (y := pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec (mults (A:=A) multA (n:=n) (invTerm (A:=A) invA (n:=n) (invTerm (A:=A) invA (n:=n) (T1 A1 n))) (mults (A:=A) multA (n:=n) (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n) (ppc (A:=A) A1 (n:=n) a1 a0) (b:=a1) (canonical_nzeroP A A0 eqA n ltM a1 l0 Cpxa0)) l0)) (mults (A:=A) multA (n:=n) (invTerm (A:=A) invA (n:=n) (T1 A1 n)) (mults (A:=A) multA (n:=n) (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n) (ppc (A:=A) A1 (n:=n) a1 a0) (b:=a0) (canonical_nzeroP A A0 eqA n ltM a0 l Cpxa1)) l))); [ apply eqp_pluspf_com with (1 := cs); auto | idtac ].
apply (eqp_trans _ _ _ _ _ _ _ _ _ cs n) with (y := pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec (mults (A:=A) multA (n:=n) (invTerm (A:=A) invA (n:=n) (multTerm (A:=A) multA (n:=n) (T1 A1 n) (invTerm (A:=A) invA (n:=n) (T1 A1 n)))) (mults (A:=A) multA (n:=n) (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n) (ppc (A:=A) A1 (n:=n) a1 a0) (b:=a1) (canonical_nzeroP A A0 eqA n ltM a1 l0 Cpxa0)) l0)) (mults (A:=A) multA (n:=n) (invTerm (A:=A) invA (n:=n) (T1 A1 n)) (mults (A:=A) multA (n:=n) (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n) (ppc (A:=A) A1 (n:=n) a1 a0) (b:=a0) (canonical_nzeroP A A0 eqA n ltM a0 l Cpxa1)) l))); [ apply eqp_pluspf_com with (1 := cs); auto | idtac ].
apply (eqp_trans _ _ _ _ _ _ _ _ _ cs n) with (y := pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec (mults (A:=A) multA (n:=n) (multTerm (A:=A) multA (n:=n) (invTerm (A:=A) invA (n:=n) (T1 A1 n)) (invTerm (A:=A) invA (n:=n) (T1 A1 n))) (mults (A:=A) multA (n:=n) (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n) (ppc (A:=A) A1 (n:=n) a1 a0) (b:=a1) (canonical_nzeroP A A0 eqA n ltM a1 l0 Cpxa0)) l0)) (mults (A:=A) multA (n:=n) (invTerm (A:=A) invA (n:=n) (T1 A1 n)) (mults (A:=A) multA (n:=n) (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n) (ppc (A:=A) A1 (n:=n) a1 a0) (b:=a0) (canonical_nzeroP A A0 eqA n ltM a0 l Cpxa1)) l))); [ apply eqp_pluspf_com with (1 := cs); auto; apply (eqp_sym _ _ _ _ _ _ _ _ _ cs n); auto | idtac ].
apply (eqp_trans _ _ _ _ _ _ _ _ _ cs n) with (y := pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec (mults (A:=A) multA (n:=n) (invTerm (A:=A) invA (n:=n) (T1 A1 n)) (mults (A:=A) multA (n:=n) (invTerm (A:=A) invA (n:=n) (T1 A1 n)) (mults (A:=A) multA (n:=n) (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n) (ppc (A:=A) A1 (n:=n) a1 a0) (b:=a1) (canonical_nzeroP A A0 eqA n ltM a1 l0 Cpxa0)) l0))) (mults (A:=A) multA (n:=n) (invTerm (A:=A) invA (n:=n) (T1 A1 n)) (mults (A:=A) multA (n:=n) (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n) (ppc (A:=A) A1 (n:=n) a1 a0) (b:=a0) (canonical_nzeroP A A0 eqA n ltM a0 l Cpxa1)) l))); [ apply eqp_pluspf_com with (1 := cs); auto | idtac ].
apply canonical_mults with (1 := cs); auto.
apply (eqp_trans _ _ _ _ _ _ _ _ _ cs n) with (y := mults (A:=A) multA (n:=n) (invTerm (A:=A) invA (n:=n) (T1 A1 n)) (pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec (mults (A:=A) multA (n:=n) (invTerm (A:=A) invA (n:=n) (T1 A1 n)) (mults (A:=A) multA (n:=n) (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n) (ppc (A:=A) A1 (n:=n) a1 a0) (b:=a1) (canonical_nzeroP A A0 eqA n ltM a1 l0 Cpxa0)) l0)) (mults (A:=A) multA (n:=n) (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n) (ppc (A:=A) A1 (n:=n) a1 a0) (b:=a0) (canonical_nzeroP A A0 eqA n ltM a0 l Cpxa1)) l))).
apply (eqp_sym _ _ _ _ _ _ _ _ _ cs n); auto.
apply mults_dist_pluspf with (1 := cs); auto.
apply (eqp_trans _ _ _ _ _ _ _ _ _ cs n) with (y := mults (A:=A) multA (n:=n) (invTerm (A:=A) invA (n:=n) (T1 A1 n)) (pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec (mults (A:=A) multA (n:=n) (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n) (ppc (A:=A) A1 (n:=n) a1 a0) (b:=a0) (canonical_nzeroP A A0 eqA n ltM a0 l Cpxa1)) l) (mults (A:=A) multA (n:=n) (invTerm (A:=A) invA (n:=n) (T1 A1 n)) (mults (A:=A) multA (n:=n) (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n) (ppc (A:=A) A1 (n:=n) a1 a0) (b:=a1) (canonical_nzeroP A A0 eqA n ltM a1 l0 Cpxa0)) l0)))).
apply (eqp_sym _ _ _ _ _ _ _ _ _ cs n); auto.
apply mults_comp with (1 := cs); auto.
apply (eqp_trans _ _ _ _ _ _ _ _ _ cs n) with (y := pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec (mults (A:=A) multA (n:=n) (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n) (ppc (A:=A) A1 (n:=n) a0 a1) (b:=a0) (canonical_nzeroP A A0 eqA n ltM a0 l Cpxa1)) l) (mults (A:=A) multA (n:=n) (invTerm (A:=A) invA (n:=n) (T1 A1 n)) (mults (A:=A) multA (n:=n) (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n) (ppc (A:=A) A1 (n:=n) a0 a1) (b:=a1) (canonical_nzeroP A A0 eqA n ltM a1 l0 Cpxa0)) l0))); auto.
apply (eqp_sym _ _ _ _ _ _ _ _ _ cs n); auto.
apply eqp_pluspf_com with (1 := cs); auto.
Admitted.

Theorem spolyf_def : forall (a b : Term A n) (nZa : ~ zeroP (A:=A) A0 eqA (n:=n) a) (nZb : ~ zeroP (A:=A) A0 eqA (n:=n) b) (p q : list (Term A n)) (Cpxa : canonical A0 eqA ltM (pX a p)) (Cpxb : canonical A0 eqA ltM (pX b q)), eqP A eqA n (spolyf (pX a p) (pX b q) Cpxa Cpxb) (minuspf A A0 A1 eqA invA minusA multA eqA_dec n ltM ltM_dec (mults (A:=A) multA (n:=n) (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n) (ppc (A:=A) A1 (n:=n) a b) (b:=a) nZa) p) (mults (A:=A) multA (n:=n) (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n) (ppc (A:=A) A1 (n:=n) a b) (b:=b) nZb) q)).
intros a b nZa nZb p q Cpxa Cpxb; simpl in |- *; auto.
cut (canonical A0 eqA ltM p); [ intros Op1 | auto ]; auto.
cut (canonical A0 eqA ltM q); [ intros Op2 | auto ]; unfold LetP in |- *; simpl in |- *; auto.
apply canonical_imp_canonical with (a := b); auto.
Admitted.

Theorem eqTerm_spolyf_red2 : forall (a b c : Term A n) (nZa : ~ zeroP (A:=A) A0 eqA (n:=n) a) (nZb : ~ zeroP (A:=A) A0 eqA (n:=n) b) (nZppab : ~ zeroP (A:=A) A0 eqA (n:=n) (ppc (A:=A) A1 (n:=n) a b)), divP A A0 eqA multA divA n c a -> divP A A0 eqA multA divA n c b -> forall (p q r : list (Term A n)) (Cpxa : canonical A0 eqA ltM (pX a p)) (Cpxb : canonical A0 eqA ltM (pX b q)), canonical A0 eqA ltM r -> eqP A eqA n (mults (A:=A) multA (n:=n) (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n) c (b:=ppc (A:=A) A1 (n:=n) a b) nZppab) (spolyf (pX a p) (pX b q) Cpxa Cpxb)) (minuspf A A0 A1 eqA invA minusA multA eqA_dec n ltM ltM_dec (spminusf A A0 A1 eqA invA minusA multA divA eqA_dec n ltM ltM_dec c b nZb r q) (spminusf A A0 A1 eqA invA minusA multA divA eqA_dec n ltM ltM_dec c a nZa r p)).
intros a b c nZa nZb nZppab H' H'0 p q r Cpxa Cpxb H'4.
cut (canonical A0 eqA ltM p); [ intros Op | apply canonical_imp_canonical with (a := a); auto ].
cut (canonical A0 eqA ltM q); [ intros Oq | apply canonical_imp_canonical with (a := b); auto ].
cut (divP A A0 eqA multA divA n (ppc (A:=A) A1 (n:=n) a b) a); [ intros div1 | apply divP_ppcl with (1 := cs); auto ].
cut (divP A A0 eqA multA divA n (ppc (A:=A) A1 (n:=n) a b) b); [ intros div2 | apply divP_ppcr with (1 := cs); auto ].
cut (divP A A0 eqA multA divA n c (ppc (A:=A) A1 (n:=n) a b)); [ intros div3 | elim ppc_is_ppcm with (1 := cs); auto ].
apply (eqp_trans _ _ _ _ _ _ _ _ _ cs n) with (y := mults (A:=A) multA (n:=n) (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n) c (b:=ppc (A:=A) A1 (n:=n) a b) nZppab) (pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec (mults (A:=A) multA (n:=n) (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n) (ppc (A:=A) A1 (n:=n) a b) (b:=a) nZa) p) (mults (A:=A) multA (n:=n) (invTerm (A:=A) invA (n:=n) (T1 A1 n)) (mults (A:=A) multA (n:=n) (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n) (ppc (A:=A) A1 (n:=n) a b) (b:=b) nZb) q)))).
apply mults_comp with (1 := cs); auto.
apply (eqp_trans _ _ _ _ _ _ _ _ _ cs n) with (y := minuspf A A0 A1 eqA invA minusA multA eqA_dec n ltM ltM_dec (mults (A:=A) multA (n:=n) (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n) (ppc (A:=A) A1 (n:=n) a b) (b:=a) nZa) p) (mults (A:=A) multA (n:=n) (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n) (ppc (A:=A) A1 (n:=n) a b) (b:=b) nZb) q)); auto.
cut (~ zeroP (A:=A) A0 eqA (n:=n) c); [ intros Z2 | inversion_clear H'0; auto ].
apply (eqp_trans _ _ _ _ _ _ _ _ _ cs n) with (y := pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec (mults (A:=A) multA (n:=n) (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n) c (b:=ppc (A:=A) A1 (n:=n) a b) nZppab) (mults (A:=A) multA (n:=n) (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n) (ppc (A:=A) A1 (n:=n) a b) (b:=a) nZa) p)) (mults (A:=A) multA (n:=n) (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n) c (b:=ppc (A:=A) A1 (n:=n) a b) nZppab) (mults (A:=A) multA (n:=n) (invTerm (A:=A) invA (n:=n) (T1 A1 n)) (mults (A:=A) multA (n:=n) (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n) (ppc (A:=A) A1 (n:=n) a b) (b:=b) nZb) q)))); [ auto | idtac ].
apply (eqp_trans _ _ _ _ _ _ _ _ _ cs n) with (y := pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec (mults (A:=A) multA (n:=n) (multTerm (A:=A) multA (n:=n) (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n) c (b:=ppc (A:=A) A1 (n:=n) a b) nZppab) (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n) (ppc (A:=A) A1 (n:=n) a b) (b:=a) nZa)) p) (mults (A:=A) multA (n:=n) (multTerm (A:=A) multA (n:=n) (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n) c (b:=ppc (A:=A) A1 (n:=n) a b) nZppab) (invTerm (A:=A) invA (n:=n) (T1 A1 n))) (mults (A:=A) multA (n:=n) (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n) (ppc (A:=A) A1 (n:=n) a b) (b:=b) nZb) q))).
apply (eqp_sym _ _ _ _ _ _ _ _ _ cs n); auto.
apply eqp_pluspf_com with (1 := cs); auto.
apply (eqp_trans _ _ _ _ _ _ _ _ _ cs n) with (y := pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec (mults (A:=A) multA (n:=n) (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n) c (b:=a) nZa) p) (mults (A:=A) multA (n:=n) (multTerm (A:=A) multA (n:=n) (invTerm (A:=A) invA (n:=n) (T1 A1 n)) (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n) c (b:=ppc (A:=A) A1 (n:=n) a b) nZppab)) (mults (A:=A) multA (n:=n) (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n) (ppc (A:=A) A1 (n:=n) a b) (b:=b) nZb) q))); [ auto | idtac ].
apply (eqp_sym _ _ _ _ _ _ _ _ _ cs n); auto.
apply eqp_pluspf_com with (1 := cs); auto.
apply mults_comp with (1 := cs); auto.
apply divTerm_compo with (1 := cs); auto.
apply (eqp_trans _ _ _ _ _ _ _ _ _ cs n) with (y := pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec (mults (A:=A) multA (n:=n) (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n) c (b:=a) nZa) p) (mults (A:=A) multA (n:=n) (invTerm (A:=A) invA (n:=n) (T1 A1 n)) (mults (A:=A) multA (n:=n) (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n) c (b:=ppc (A:=A) A1 (n:=n) a b) nZppab) (mults (A:=A) multA (n:=n) (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n) (ppc (A:=A) A1 (n:=n) a b) (b:=b) nZb) q)))).
apply eqp_pluspf_com with (1 := cs); auto.
apply (eqp_trans _ _ _ _ _ _ _ _ _ cs n) with (y := pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec (mults (A:=A) multA (n:=n) (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n) c (b:=a) nZa) p) (mults (A:=A) multA (n:=n) (invTerm (A:=A) invA (n:=n) (T1 A1 n)) (mults (A:=A) multA (n:=n) (multTerm (A:=A) multA (n:=n) (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n) c (b:=ppc (A:=A) A1 (n:=n) a b) nZppab) (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n) (ppc (A:=A) A1 (n:=n) a b) (b:=b) nZb)) q))).
apply (eqp_sym _ _ _ _ _ _ _ _ _ cs n); apply eqp_pluspf_com with (1 := cs); auto.
apply (eqp_trans _ _ _ _ _ _ _ _ _ cs n) with (y := pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec (mults (A:=A) multA (n:=n) (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n) c (b:=a) nZa) p) (mults (A:=A) multA (n:=n) (invTerm (A:=A) invA (n:=n) (T1 A1 n)) (mults (A:=A) multA (n:=n) (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n) c (b:=b) nZb) q))).
apply eqp_pluspf_com with (1 := cs); auto.
apply (eqp_sym _ _ _ _ _ _ _ _ _ cs n); auto.
apply mults_comp with (1 := cs); auto.
apply mults_comp with (1 := cs); auto.
apply divTerm_compo with (1 := cs); auto.
apply (eqp_trans _ _ _ _ _ _ _ _ _ cs n) with (y := pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec (mults (A:=A) multA (n:=n) (invTerm (A:=A) invA (n:=n) (T1 A1 n)) (mults (A:=A) multA (n:=n) (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n) c (b:=b) nZb) q)) (mults (A:=A) multA (n:=n) (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n) c (b:=a) nZa) p)); [ auto | idtac ].
apply (eqp_trans _ _ _ _ _ _ _ _ _ cs n) with (y := pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec (mults (A:=A) multA (n:=n) (invTerm (A:=A) invA (n:=n) (T1 A1 n)) (mults (A:=A) multA (n:=n) (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n) c (b:=b) nZb) q)) (pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec (pO A n) (mults (A:=A) multA (n:=n) (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n) c (b:=a) nZa) p))).
apply (eqp_sym _ _ _ _ _ _ _ _ _ cs n); auto.
apply (eqp_trans _ _ _ _ _ _ _ _ _ cs n) with (y := pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec (mults (A:=A) multA (n:=n) (invTerm (A:=A) invA (n:=n) (T1 A1 n)) (mults (A:=A) multA (n:=n) (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n) c (b:=b) nZb) q)) (pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec (minuspf A A0 A1 eqA invA minusA multA eqA_dec n ltM ltM_dec r r) (mults (A:=A) multA (n:=n) (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n) c (b:=a) nZa) p))).
apply eqp_pluspf_com with (1 := cs); auto.
apply eqp_pluspf_com with (1 := cs); auto.
apply (eqp_sym _ _ _ _ _ _ _ _ _ cs n); apply minuspf_refl with (1 := cs); auto.
apply (eqp_trans _ _ _ _ _ _ _ _ _ cs n) with (y := pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec (mults (A:=A) multA (n:=n) (invTerm (A:=A) invA (n:=n) (T1 A1 n)) (mults (A:=A) multA (n:=n) (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n) c (b:=b) nZb) q)) (pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec (pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec r (mults (A:=A) multA (n:=n) (invTerm (A:=A) invA (n:=n) (T1 A1 n)) r)) (mults (A:=A) multA (n:=n) (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n) c (b:=a) nZa) p))).
apply eqp_pluspf_com with (1 := cs); auto.
apply (eqp_sym _ _ _ _ _ _ _ _ _ cs n); auto.
apply (eqp_sym _ _ _ _ _ _ _ _ _ cs n); auto.
apply (eqp_trans _ _ _ _ _ _ _ _ _ cs n) with (y := pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec (mults (A:=A) multA (n:=n) (invTerm (A:=A) invA (n:=n) (T1 A1 n)) (mults (A:=A) multA (n:=n) (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n) c (b:=b) nZb) q)) (pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec r (pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec (mults (A:=A) multA (n:=n) (invTerm (A:=A) invA (n:=n) (T1 A1 n)) r) (mults (A:=A) multA (n:=n) (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n) c (b:=a) nZa) p)))).
apply eqp_pluspf_com with (1 := cs); auto.
apply (eqp_trans _ _ _ _ _ _ _ _ _ cs n) with (y := pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec (pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec (mults (A:=A) multA (n:=n) (invTerm (A:=A) invA (n:=n) (T1 A1 n)) (mults (A:=A) multA (n:=n) (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n) c (b:=b) nZb) q)) r) (pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec (mults (A:=A) multA (n:=n) (invTerm (A:=A) invA (n:=n) (T1 A1 n)) r) (mults (A:=A) multA (n:=n) (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n) c (b:=a) nZa) p))).
apply (eqp_sym _ _ _ _ _ _ _ _ _ cs n); auto.
apply (eqp_trans _ _ _ _ _ _ _ _ _ cs n) with (y := pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec (pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec r (mults (A:=A) multA (n:=n) (invTerm (A:=A) invA (n:=n) (T1 A1 n)) (mults (A:=A) multA (n:=n) (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n) c (b:=b) nZb) q))) (pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec (mults (A:=A) multA (n:=n) (invTerm (A:=A) invA (n:=n) (T1 A1 n)) r) (mults (A:=A) multA (n:=n) (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n) c (b:=a) nZa) p))).
apply eqp_pluspf_com with (1 := cs); auto.
apply (eqp_trans _ _ _ _ _ _ _ _ _ cs n) with (y := pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec (minuspf A A0 A1 eqA invA minusA multA eqA_dec n ltM ltM_dec r (mults (A:=A) multA (n:=n) (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n) c (b:=b) nZb) q)) (pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec (mults (A:=A) multA (n:=n) (invTerm (A:=A) invA (n:=n) (T1 A1 n)) r) (mults (A:=A) multA (n:=n) (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n) c (b:=a) nZa) p))).
apply eqp_pluspf_com with (1 := cs); auto.
apply (eqp_sym _ _ _ _ _ _ _ _ _ cs n); auto.
apply (eqp_trans _ _ _ _ _ _ _ _ _ cs n) with (y := pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec (minuspf A A0 A1 eqA invA minusA multA eqA_dec n ltM ltM_dec r (mults (A:=A) multA (n:=n) (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n) c (b:=b) nZb) q)) (pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec (mults (A:=A) multA (n:=n) (invTerm (A:=A) invA (n:=n) (T1 A1 n)) r) (mults (A:=A) multA (n:=n) (T1 A1 n) (mults (A:=A) multA (n:=n) (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n) c (b:=a) nZa) p)))).
apply (eqp_sym _ _ _ _ _ _ _ _ _ cs n); auto.
apply eqp_pluspf_com with (1 := cs); auto.
apply (eqp_trans _ _ _ _ _ _ _ _ _ cs n) with (y := pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec (minuspf A A0 A1 eqA invA minusA multA eqA_dec n ltM ltM_dec r (mults (A:=A) multA (n:=n) (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n) c (b:=b) nZb) q)) (pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec (mults (A:=A) multA (n:=n) (invTerm (A:=A) invA (n:=n) (T1 A1 n)) r) (mults (A:=A) multA (n:=n) (invTerm (A:=A) invA (n:=n) (invTerm (A:=A) invA (n:=n) (T1 A1 n))) (mults (A:=A) multA (n:=n) (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n) c (b:=a) nZa) p)))).
apply eqp_pluspf_com with (1 := cs); auto.
apply (eqp_trans _ _ _ _ _ _ _ _ _ cs n) with (y := pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec (minuspf A A0 A1 eqA invA minusA multA eqA_dec n ltM ltM_dec r (mults (A:=A) multA (n:=n) (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n) c (b:=b) nZb) q)) (pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec (mults (A:=A) multA (n:=n) (invTerm (A:=A) invA (n:=n) (T1 A1 n)) r) (mults (A:=A) multA (n:=n) (invTerm (A:=A) invA (n:=n) (multTerm (A:=A) multA (n:=n) (T1 A1 n) (invTerm (A:=A) invA (n:=n) (T1 A1 n)))) (mults (A:=A) multA (n:=n) (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n) c (b:=a) nZa) p)))); auto.
apply eqp_pluspf_com with (1 := cs); auto.
apply canonical_pluspf; auto.
apply eqp_pluspf_com with (1 := cs); auto.
apply (eqp_trans _ _ _ _ _ _ _ _ _ cs n) with (y := pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec (minuspf A A0 A1 eqA invA minusA multA eqA_dec n ltM ltM_dec r (mults (A:=A) multA (n:=n) (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n) c (b:=b) nZb) q)) (pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec (mults (A:=A) multA (n:=n) (invTerm (A:=A) invA (n:=n) (T1 A1 n)) r) (mults (A:=A) multA (n:=n) (multTerm (A:=A) multA (n:=n) (invTerm (A:=A) invA (n:=n) (T1 A1 n)) (invTerm (A:=A) invA (n:=n) (T1 A1 n))) (mults (A:=A) multA (n:=n) (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n) c (b:=a) nZa) p)))).
apply eqp_pluspf_com with (1 := cs); auto.
apply canonical_pluspf; auto.
apply eqp_pluspf_com with (1 := cs); auto.
apply (eqp_sym _ _ _ _ _ _ _ _ _ cs n); auto.
apply (eqp_trans _ _ _ _ _ _ _ _ _ cs n) with (y := pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec (minuspf A A0 A1 eqA invA minusA multA eqA_dec n ltM ltM_dec r (mults (A:=A) multA (n:=n) (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n) c (b:=b) nZb) q)) (pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec (mults (A:=A) multA (n:=n) (invTerm (A:=A) invA (n:=n) (T1 A1 n)) r) (mults (A:=A) multA (n:=n) (invTerm (A:=A) invA (n:=n) (T1 A1 n)) (mults (A:=A) multA (n:=n) (invTerm (A:=A) invA (n:=n) (T1 A1 n)) (mults (A:=A) multA (n:=n) (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n) c (b:=a) nZa) p))))).
apply eqp_pluspf_com with (1 := cs); auto.
apply canonical_pluspf; auto.
apply eqp_pluspf_com with (1 := cs); auto.
apply (eqp_trans _ _ _ _ _ _ _ _ _ cs n) with (y := pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec (minuspf A A0 A1 eqA invA minusA multA eqA_dec n ltM ltM_dec r (mults (A:=A) multA (n:=n) (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n) c (b:=b) nZb) q)) (mults (A:=A) multA (n:=n) (invTerm (A:=A) invA (n:=n) (T1 A1 n)) (pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec r (mults (A:=A) multA (n:=n) (invTerm (A:=A) invA (n:=n) (T1 A1 n)) (mults (A:=A) multA (n:=n) (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n) c (b:=a) nZa) p))))).
apply eqp_pluspf_com with (1 := cs); auto.
apply canonical_pluspf; auto.
apply canonical_mults with (1 := cs); auto.
apply (eqp_sym _ _ _ _ _ _ _ _ _ cs n); auto.
apply (eqp_trans _ _ _ _ _ _ _ _ _ cs n) with (y := pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec (minuspf A A0 A1 eqA invA minusA multA eqA_dec n ltM ltM_dec r (mults (A:=A) multA (n:=n) (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n) c (b:=b) nZb) q)) (mults (A:=A) multA (n:=n) (invTerm (A:=A) invA (n:=n) (T1 A1 n)) (minuspf A A0 A1 eqA invA minusA multA eqA_dec n ltM ltM_dec r (mults (A:=A) multA (n:=n) (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n) c (b:=a) nZa) p)))).
apply (eqp_sym _ _ _ _ _ _ _ _ _ cs n); auto.
apply eqp_pluspf_com with (1 := cs); auto.
apply canonical_mults with (1 := cs); auto.
Admitted.

Theorem eqTerm_spolyf_red3 : forall (a b : Term A n) (nZa : ~ zeroP (A:=A) A0 eqA (n:=n) a) (nZb : ~ zeroP (A:=A) A0 eqA (n:=n) b) (p q r : list (Term A n)) (Cpxa : canonical A0 eqA ltM (pX a p)) (Cpxb : canonical A0 eqA ltM (pX b q)), canonical A0 eqA ltM r -> eqP A eqA n (spolyf (pX a p) (pX b q) Cpxa Cpxb) (minuspf A A0 A1 eqA invA minusA multA eqA_dec n ltM ltM_dec (spminusf A A0 A1 eqA invA minusA multA divA eqA_dec n ltM ltM_dec (ppc (A:=A) A1 (n:=n) a b) b nZb r q) (spminusf A A0 A1 eqA invA minusA multA divA eqA_dec n ltM ltM_dec (ppc (A:=A) A1 (n:=n) a b) a nZa r p)).
intros a b nZa nZb p q r Cpxa Cpxb H'1.
cut (~ zeroP (A:=A) A0 eqA (n:=n) (ppc (A:=A) A1 (n:=n) a b)); [ intros nZppab | auto ].
apply (eqp_trans _ _ _ _ _ _ _ _ _ cs n) with (y := mults (A:=A) multA (n:=n) (T1 A1 n) (spolyf (pX a p) (pX b q) Cpxa Cpxb)).
apply (eqp_sym _ _ _ _ _ _ _ _ _ cs n); auto.
apply (eqp_trans _ _ _ _ _ _ _ _ _ cs n) with (y := mults (A:=A) multA (n:=n) (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n) (ppc (A:=A) A1 (n:=n) a b) (b:=ppc (A:=A) A1 (n:=n) a b) nZppab) (spolyf (pX a p) (pX b q) Cpxa Cpxb)).
apply (eqp_sym _ _ _ _ _ _ _ _ _ cs n); auto.
Admitted.

Theorem spoly_is_minus : forall (a b : Term A n) (nZa : ~ zeroP (A:=A) A0 eqA (n:=n) a) (nZb : ~ zeroP (A:=A) A0 eqA (n:=n) b) (p q : list (Term A n)) (Cpxa : canonical A0 eqA ltM (pX a p)) (Cpxb : canonical A0 eqA ltM (pX b q)), eqP A eqA n (spolyf (pX a p) (pX b q) Cpxa Cpxb) (minuspf A A0 A1 eqA invA minusA multA eqA_dec n ltM ltM_dec (mults (A:=A) multA (n:=n) (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n) (ppc (A:=A) A1 (n:=n) a b) (b:=a) nZa) (pX a p)) (mults (A:=A) multA (n:=n) (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n) (ppc (A:=A) A1 (n:=n) a b) (b:=b) nZb) (pX b q))).
simpl in |- *; unfold LetP in |- *; simpl in |- *.
intros a b nZa nZb p q Cpxa Cpxb.
cut (canonical A0 eqA ltM p); [ intros Op | apply canonical_imp_canonical with (a := a); auto ].
cut (canonical A0 eqA ltM q); [ intros Oq | apply canonical_imp_canonical with (a := b); auto ].
cut (~ zeroP (A:=A) A0 eqA (n:=n) (ppc (A:=A) A1 (n:=n) a b)); [ intros nZppab | auto ].
apply (eqp_trans _ _ _ _ _ _ _ _ _ cs n) with (minuspf A A0 A1 eqA invA minusA multA eqA_dec n ltM ltM_dec (mults (A:=A) multA (n:=n) (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n) (ppc (A:=A) A1 (n:=n) a b) (b:=a) nZa) p) (mults (A:=A) multA (n:=n) (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n) (ppc (A:=A) A1 (n:=n) a b) (b:=b) nZb) q)); auto.
apply (eqp_trans _ _ _ _ _ _ _ _ _ cs n) with (y := minuspf A A0 A1 eqA invA minusA multA eqA_dec n ltM ltM_dec (pX (ppc (A:=A) A1 (n:=n) a b) (mults (A:=A) multA (n:=n) (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n) (ppc (A:=A) A1 (n:=n) a b) (b:=a) nZa) p)) (pX (ppc (A:=A) A1 (n:=n) a b) (mults (A:=A) multA (n:=n) (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n) (ppc (A:=A) A1 (n:=n) a b) (b:=b) nZb) q))).
apply (eqp_sym _ _ _ _ _ _ _ _ _ cs n).
apply minuspf_zero with (1 := cs); auto.
cut (eqTerm (A:=A) eqA (n:=n) (ppc (A:=A) A1 (n:=n) a b) (multTerm (A:=A) multA (n:=n) (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n) (ppc (A:=A) A1 (n:=n) a b) (b:=a) nZa) a)); [ intros Z2 | auto ].
cut (eqTerm (A:=A) eqA (n:=n) (ppc (A:=A) A1 (n:=n) a b) (multTerm (A:=A) multA (n:=n) (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n) (ppc (A:=A) A1 (n:=n) a b) (b:=b) nZb) b)); [ intros Z3 | auto ].
apply minuspf_comp with (1 := cs); auto.
apply canonical_pX_eqT with (a := multTerm (A:=A) multA (n:=n) (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n) (ppc (A:=A) A1 (n:=n) a b) (b:=a) nZa) a); auto.
change (canonical A0 eqA ltM (mults (A:=A) multA (n:=n) (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n) (ppc (A:=A) A1 (n:=n) a b) (b:=a) nZa) (pX a p))) in |- *; auto.
apply (eqT_sym A n); apply (eqTerm_imp_eqT A eqA n); auto.
apply canonical_pX_eqT with (a := multTerm (A:=A) multA (n:=n) (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n) (ppc (A:=A) A1 (n:=n) a b) (b:=b) nZb) b); auto.
change (canonical A0 eqA ltM (mults (A:=A) multA (n:=n) (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n) (ppc (A:=A) A1 (n:=n) a b) (b:=b) nZb) (pX b q))) in |- *; auto.
apply (eqT_sym A n); apply (eqTerm_imp_eqT A eqA n); auto.
change (canonical A0 eqA ltM (mults (A:=A) multA (n:=n) (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n) (ppc (A:=A) A1 (n:=n) a b) (b:=a) nZa) (pX a p))) in |- *; auto.
Admitted.

Theorem spoly_div_is_minus : forall (a b c : Term A n) (nZa : ~ zeroP (A:=A) A0 eqA (n:=n) a) (nZb : ~ zeroP (A:=A) A0 eqA (n:=n) b) (nZppab : ~ zeroP (A:=A) A0 eqA (n:=n) (ppc (A:=A) A1 (n:=n) a b)), divP A A0 eqA multA divA n c a -> divP A A0 eqA multA divA n c b -> forall (p q : list (Term A n)) (Cpxa : canonical A0 eqA ltM (pX a p)) (Cpxb : canonical A0 eqA ltM (pX b q)), eqP A eqA n (mults (A:=A) multA (n:=n) (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n) c (b:=ppc (A:=A) A1 (n:=n) a b) nZppab) (spolyf (pX a p) (pX b q) Cpxa Cpxb)) (minuspf A A0 A1 eqA invA minusA multA eqA_dec n ltM ltM_dec (mults (A:=A) multA (n:=n) (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n) c (b:=a) nZa) (pX a p)) (mults (A:=A) multA (n:=n) (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n) c (b:=b) nZb) (pX b q))).
intros a b c nZa nZb nZppab H' H'0 p q Cpxa Cpxb.
cut (canonical A0 eqA ltM p); [ intros Op | apply canonical_imp_canonical with (a := a) ]; auto.
cut (canonical A0 eqA ltM q); [ intros Oq | apply canonical_imp_canonical with (a := b) ]; auto.
cut (~ zeroP (A:=A) A0 eqA (n:=n) c); [ intros Z2 | idtac ].
cut (divP A A0 eqA multA divA n c (ppc (A:=A) A1 (n:=n) a b)); [ intros div1 | idtac ].
apply (eqp_trans _ _ _ _ _ _ _ _ _ cs n) with (y := mults (A:=A) multA (n:=n) (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n) c (b:=ppc (A:=A) A1 (n:=n) a b) nZppab) (minuspf A A0 A1 eqA invA minusA multA eqA_dec n ltM ltM_dec (mults (A:=A) multA (n:=n) (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n) (ppc (A:=A) A1 (n:=n) a b) (b:=a) nZa) (pX a p)) (mults (A:=A) multA (n:=n) (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n) (ppc (A:=A) A1 (n:=n) a b) (b:=b) nZb) (pX b q)))).
apply mults_comp with (1 := cs); auto.
apply spoly_is_minus; auto.
apply (eqp_trans _ _ _ _ _ _ _ _ _ cs n) with (y := minuspf A A0 A1 eqA invA minusA multA eqA_dec n ltM ltM_dec (mults (A:=A) multA (n:=n) (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n) c (b:=ppc (A:=A) A1 (n:=n) a b) nZppab) (mults (A:=A) multA (n:=n) (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n) (ppc (A:=A) A1 (n:=n) a b) (b:=a) nZa) (pX a p))) (mults (A:=A) multA (n:=n) (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n) c (b:=ppc (A:=A) A1 (n:=n) a b) nZppab) (mults (A:=A) multA (n:=n) (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n) (ppc (A:=A) A1 (n:=n) a b) (b:=b) nZb) (pX b q)))).
apply mults_dist_minuspf with (1 := cs); auto.
apply (eqp_trans _ _ _ _ _ _ _ _ _ cs n) with (y := minuspf A A0 A1 eqA invA minusA multA eqA_dec n ltM ltM_dec (mults (A:=A) multA (n:=n) (multTerm (A:=A) multA (n:=n) (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n) c (b:=ppc (A:=A) A1 (n:=n) a b) nZppab) (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n) (ppc (A:=A) A1 (n:=n) a b) (b:=a) nZa)) (pX a p)) (mults (A:=A) multA (n:=n) (multTerm (A:=A) multA (n:=n) (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n) c (b:=ppc (A:=A) A1 (n:=n) a b) nZppab) (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n) (ppc (A:=A) A1 (n:=n) a b) (b:=b) nZb)) (pX b q))).
apply minuspf_comp with (1 := cs); auto; apply (eqp_sym _ _ _ _ _ _ _ _ _ cs n); auto.
apply minuspf_comp with (1 := cs); auto.
apply mults_comp with (1 := cs); auto.
apply (eqTerm_sym _ _ _ _ _ _ _ _ _ cs n); apply divTerm_compo with (1 := cs); auto.
apply mults_comp with (1 := cs); auto.
apply (eqTerm_sym _ _ _ _ _ _ _ _ _ cs n); apply divTerm_compo with (1 := cs); auto.
case ppc_is_ppcm with (1 := cs) (a := a) (b := b); auto.
Admitted.

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
Admitted.

Theorem Conf_inv1 : forall (Q : list (poly A0 eqA ltM)) (a b c : Term A n) (nZb : ~ zeroP (A:=A) A0 eqA (n:=n) b) (nZc : ~ zeroP (A:=A) A0 eqA (n:=n) c) (p q r r1 s1 : list (Term A n)), Confluent Q (pX a p) (pX b q) (pX c r) -> reducestar A A0 A1 eqA invA minusA multA divA eqA_dec n ltM ltM_dec Q (spminusf A A0 A1 eqA invA minusA multA divA eqA_dec n ltM ltM_dec a b nZb p q) r1 -> reducestar A A0 A1 eqA invA minusA multA divA eqA_dec n ltM ltM_dec Q (spminusf A A0 A1 eqA invA minusA multA divA eqA_dec n ltM ltM_dec a c nZc p r) s1 -> eqP A eqA n r1 s1.
intros Q a b c nZb nZc p q r r1 s1 H'0 H'1 H'2; inversion_clear H'0.
apply H.
rewrite sp_rew with (1 := cs) (a := a) (b := b) (nZ2 := nZb); auto.
Admitted.

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
