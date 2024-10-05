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

Theorem Conf_inv1 : forall (Q : list (poly A0 eqA ltM)) (a b c : Term A n) (nZb : ~ zeroP (A:=A) A0 eqA (n:=n) b) (nZc : ~ zeroP (A:=A) A0 eqA (n:=n) c) (p q r r1 s1 : list (Term A n)), Confluent Q (pX a p) (pX b q) (pX c r) -> reducestar A A0 A1 eqA invA minusA multA divA eqA_dec n ltM ltM_dec Q (spminusf A A0 A1 eqA invA minusA multA divA eqA_dec n ltM ltM_dec a b nZb p q) r1 -> reducestar A A0 A1 eqA invA minusA multA divA eqA_dec n ltM ltM_dec Q (spminusf A A0 A1 eqA invA minusA multA divA eqA_dec n ltM ltM_dec a c nZc p r) s1 -> eqP A eqA n r1 s1.
intros Q a b c nZb nZc p q r r1 s1 H'0 H'1 H'2; inversion_clear H'0.
apply H.
rewrite sp_rew with (1 := cs) (a := a) (b := b) (nZ2 := nZb); auto.
rewrite sp_rew with (1 := cs) (a := a) (b := c) (nZ2 := nZc); auto.
