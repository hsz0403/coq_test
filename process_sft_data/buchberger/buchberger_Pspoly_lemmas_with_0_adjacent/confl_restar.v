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

Theorem confl_restar : forall Q : list (poly A0 eqA ltM), SpolyQ Q -> forall p : poly A0 eqA ltM, ReduStarConfluent Q (s2p A A0 eqA n ltM p).
intros Q H'.
intros p; pattern p in |- *; apply well_founded_ind with (R := sltP (A:=A) (A0:=A0) (eqA:=eqA) (n:=n) (ltM:=ltM)); auto.
apply sltp_wf; auto.
intros x; elim x; clear x.
intros x Op_x Rec; simpl in |- *.
apply ReduStarConfluent0; auto.
intros r s H'1 H'2.
case reducestar_inv with (1 := cs) (3 := H'2); auto; intros H'8; elim H'8; clear H'8.
case reducestar_inv with (1 := cs) (3 := H'1); auto; intros H'9; elim H'9; clear H'9.
intros H H0 H1 H2; apply (eqp_trans _ _ _ _ _ _ _ _ _ cs n) with (y := x); auto; apply (eqp_sym _ _ _ _ _ _ _ _ _ cs n); auto.
intros x0 H H0 H1; elim H; intros H2 H3; absurd (reduce A A0 A1 eqA invA minusA multA divA eqA_dec n ltM ltM_dec Q x x0); auto.
intros x0 H; elim H; intros H0 H1; clear H.
case reducestar_inv with (1 := cs) (3 := H'1); auto; intros H'9; elim H'9; clear H'9.
intros H H2; absurd (reduce A A0 A1 eqA invA minusA multA divA eqA_dec n ltM ltM_dec Q x x0); auto.
intros x1 H; elim H; intros H2 H3; clear H.
generalize H3 H0 H'1 Op_x Rec; clear H3 H0 H'1 Rec Op_x; inversion H2.
intros H'3 H'4 H'5 Op_x H'6.
generalize Op_x H'6 H'5 H'3; clear H'5 H'3 H'6 Op_x.
inversion H'4.
intros Op_x H'6 H'5 H'3.
apply confl_top with (Q := Q) (a := a) (b := b) (c := b0) (nZb := nZb) (nZc := nZb0) (p := p0) (q := q) (r := q0); auto.
intros q1 H'9 H'10.
generalize (H'6 (mks A A0 eqA n ltM q1 H'9)); simpl in |- *; auto.
apply reducetop_sp with (1 := cs); auto.
apply reducetop_sp with (1 := cs); auto.
apply reducestar_eqp_com with (1 := cs) (p := x1) (q := r); auto.
apply canonical_reduce with (1 := cs) (3 := H2); auto.
rewrite <- H4; auto.
apply (eqp_sym _ _ _ _ _ _ _ _ _ cs n); auto.
apply reducestar_eqp_com with (1 := cs) (p := x0) (q := s); auto.
apply canonical_reduce with (1 := cs) (3 := H'4); auto.
apply (eqp_sym _ _ _ _ _ _ _ _ _ cs n); auto.
intros Op_x H'6 H'5 H'3.
apply (eqp_sym _ _ _ _ _ _ _ _ _ cs n).
apply confl_mix with (Q := Q) (a := a) (b := b) (nZb := nZb) (p := p0) (q := q0) (r := q); auto.
intros q1 H'9 H'10.
generalize (H'6 (mks A A0 eqA n ltM q1 H'9)); simpl in |- *; auto.
apply reducetop_sp with (1 := cs); auto.
apply reducestar_eqp_com with (p := pX b0 q0) (q := s) (1 := cs); auto.
rewrite H9; auto.
rewrite H9.
apply canonical_reduce with (1 := cs) (3 := H'4); auto.
apply (eqp_sym _ _ _ _ _ _ _ _ _ cs n); auto.
apply reducestar_eqp_com with (1 := cs) (p := x1) (q := r); auto.
apply canonical_reduce with (1 := cs) (3 := H2); auto.
rewrite <- H4; auto.
apply (eqp_sym _ _ _ _ _ _ _ _ _ cs n); auto.
intros H'3 H'4 H'5 Op_x H'6.
inversion H'4.
apply (confl_mix Q a b0 nZb p0 q q0); auto.
intros q1 H'9 H'10.
generalize (H'6 (mks A A0 eqA n ltM q1 H'9)); simpl in |- *; auto.
apply reducetop_sp with (1 := cs); auto.
apply reducestar_eqp_com with (1 := cs) (p := pX b q) (q := r); auto.
rewrite H4; auto.
apply canonical_reduce with (1 := cs) (3 := H2); auto.
rewrite <- H3; auto.
apply (eqp_sym _ _ _ _ _ _ _ _ _ cs n); auto.
apply reducestar_eqp_com with (1 := cs) (p := x0) (q := s); auto.
apply canonical_reduce with (1 := cs) (3 := H'4); auto.
apply (eqp_sym _ _ _ _ _ _ _ _ _ cs n); auto.
apply confl_under with (Q := Q) (a := a) (p := p0) (r := q) (s := q0); auto.
intros q1 H'9 H'10.
generalize (H'6 (mks A A0 eqA n ltM q1 H'9)); simpl in |- *; auto.
apply reducestar_eqp_com with (1 := cs) (p := pX b q) (q := r); auto.
rewrite H4.
apply canonical_reduce with (1 := cs) (3 := H2); auto.
rewrite <- H3; auto.
apply (eqp_sym _ _ _ _ _ _ _ _ _ cs n); auto.
apply reducestar_eqp_com with (p := pX b0 q0) (q := s) (1 := cs); auto.
rewrite H8; auto.
rewrite H8; apply canonical_reduce with (1 := cs) (3 := H'4); auto.
apply (eqp_sym _ _ _ _ _ _ _ _ _ cs n); auto.
