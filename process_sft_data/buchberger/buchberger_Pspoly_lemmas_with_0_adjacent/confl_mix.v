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

Theorem confl_mix : forall (Q : list (poly A0 eqA ltM)) (a b : Term A n) (nZb : ~ zeroP (A:=A) A0 eqA (n:=n) b) (p q r : list (Term A n)), canonical A0 eqA ltM (pX a p) -> divP A A0 eqA multA divA n a b -> inPolySet A A0 eqA n ltM (pX b r) Q -> (forall q : list (Term A n), canonical A0 eqA ltM q -> ltP (A:=A) (n:=n) ltM q (pX a p) -> ReduStarConfluent Q q) -> reduce A A0 A1 eqA invA minusA multA divA eqA_dec n ltM ltM_dec Q (pX a p) (pX a q) -> reduce A A0 A1 eqA invA minusA multA divA eqA_dec n ltM ltM_dec Q (pX a p) (spminusf A A0 A1 eqA invA minusA multA divA eqA_dec n ltM ltM_dec a b nZb p r) -> forall r1 s1 : list (Term A n), reducestar A A0 A1 eqA invA minusA multA divA eqA_dec n ltM ltM_dec Q (pX a q) r1 -> reducestar A A0 A1 eqA invA minusA multA divA eqA_dec n ltM ltM_dec Q (spminusf A A0 A1 eqA invA minusA multA divA eqA_dec n ltM ltM_dec a b nZb p r) s1 -> eqP A eqA n r1 s1.
intros Q a b nZb p q r Op1 dviP_ab in_br Rec red1 red2 r1 s1 red3 red4.
cut (canonical A0 eqA ltM (pX b r)); [ intros Op2 | apply inPolySet_imp_canonical with (L := Q); auto ].
cut (reduce A A0 A1 eqA invA minusA multA divA eqA_dec n ltM ltM_dec Q p q); [ intros H'6 | apply reduce_inv with (1 := cs) (3 := red1); auto ].
cut (canonical A0 eqA ltM p); [ intros Op3 | apply canonical_imp_canonical with (a := a); auto ].
cut (canonical A0 eqA ltM r); [ intros Op4 | apply canonical_imp_canonical with (a := b); auto ].
cut (canonical A0 eqA ltM q); [ intros Op5 | apply canonical_reduce with (1 := cs) (3 := H'6); auto ].
case one_minus_reduceplus with (plusA := plusA) (3 := H'6) (r := mults (A:=A) multA (n:=n) (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n) a (b:=b) nZb) r); auto.
intros s H; elim H; intros H0 H1; clear H.
cut (canonical A0 eqA ltM s); [ intros Op6 | apply canonical_reduceplus with (1 := cs) (3 := H1); auto ].
elim reduce0_reducestar with (Q := Q) (p := s) (1 := cs) (ltM_dec := ltM_dec) (eqA_dec := eqA_dec); auto; intros t E.
apply (eqp_trans _ _ _ _ _ _ _ _ _ cs n) with (y := t); auto.
lapply (Rec (pX a q)); [ intros H'0; lapply H'0; [ intros H'1; elim H'1; clear H'0 | clear H'0 ] | idtac ]; auto.
intros PH'0; apply PH'0; auto.
apply (reducestar_trans A A0 A1 eqA plusA invA minusA multA divA cs eqA_dec n ltM ltM_dec os Q) with (y := s); auto.
apply canonical_reduce with (1 := cs) (3 := red1); auto.
apply Rstar_n with (y := minuspf A A0 A1 eqA invA minusA multA eqA_dec n ltM ltM_dec q (mults (A:=A) multA (n:=n) (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n) a (b:=b) nZb) r)); auto.
apply reducetop with (b := b) (nZb := nZb) (q := r); auto.
apply ltP_reduce with (1 := cs) (3 := red1); auto.
apply canonical_reduce with (1 := cs) (3 := red1); auto.
lapply (Rec (spminusf A A0 A1 eqA invA minusA multA divA eqA_dec n ltM ltM_dec a b nZb p r)); [ intros H'0; lapply H'0; [ intros H'1; elim H'1; clear H'0 | clear H'0 ] | idtac ]; auto.
intros PH'0; apply PH'0; auto.
apply (reducestar_trans A A0 A1 eqA plusA invA minusA multA divA cs eqA_dec n ltM ltM_dec os Q) with (y := s); auto.
apply canonical_spminusf with (1 := cs); auto.
apply ltP_reduce with (1 := cs) (3 := red2); auto.
apply canonical_spminusf with (1 := cs); auto.
