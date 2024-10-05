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

Theorem confl_top_simpl : forall (Q : list (poly A0 eqA ltM)) (a b c : Term A n) (nZb : ~ zeroP (A:=A) A0 eqA (n:=n) b) (nZc : ~ zeroP (A:=A) A0 eqA (n:=n) c) (p q r : list (Term A n)) (Cpxc : canonical A0 eqA ltM (pX c r)) (Cpxb : canonical A0 eqA ltM (pX b q)), reducestar A A0 A1 eqA invA minusA multA divA eqA_dec n ltM ltM_dec Q (spolyf (pX c r) (pX b q) Cpxc Cpxb) (pO A n) -> canonical A0 eqA ltM (pX a p) -> divP A A0 eqA multA divA n a b -> inPolySet A A0 eqA n ltM (pX b q) Q -> divP A A0 eqA multA divA n a c -> inPolySet A A0 eqA n ltM (pX c r) Q -> (forall q : list (Term A n), canonical A0 eqA ltM q -> ltP (A:=A) (n:=n) ltM q (pX a p) -> ReduStarConfluent Q q) -> reduce A A0 A1 eqA invA minusA multA divA eqA_dec n ltM ltM_dec Q (pX a p) (spminusf A A0 A1 eqA invA minusA multA divA eqA_dec n ltM ltM_dec a b nZb p q) -> reduce A A0 A1 eqA invA minusA multA divA eqA_dec n ltM ltM_dec Q (pX a p) (spminusf A A0 A1 eqA invA minusA multA divA eqA_dec n ltM ltM_dec a c nZc p r) -> forall r1 s1 : list (Term A n), reducestar A A0 A1 eqA invA minusA multA divA eqA_dec n ltM ltM_dec Q (spminusf A A0 A1 eqA invA minusA multA divA eqA_dec n ltM ltM_dec a b nZb p q) r1 -> reducestar A A0 A1 eqA invA minusA multA divA eqA_dec n ltM ltM_dec Q (spminusf A A0 A1 eqA invA minusA multA divA eqA_dec n ltM ltM_dec a c nZc p r) s1 -> eqP A eqA n r1 s1.
intros Q a b c nZb nZc p q r Cpxc Cpxb red_r0 Cpxa divP_ab in_bp_Q divP_ac in_cr_Q Rec red1 red2 r1 s1 reds1 reds2.
cut (canonical A0 eqA ltM p); [ intros Op1 | apply canonical_imp_canonical with a; auto ].
cut (canonical A0 eqA ltM r); [ intros Op2 | apply canonical_imp_canonical with c; auto ].
cut (canonical A0 eqA ltM q); [ intros Op3 | apply canonical_imp_canonical with b; auto ].
cut (~ zeroP (A:=A) A0 eqA (n:=n) a); [ intros nZa | idtac ].
cut (~ zeroP (A:=A) A0 eqA (n:=n) (ppc (A:=A) A1 (n:=n) c b)); [ intros nZppcd | idtac ].
cut (eqP A eqA n (mults (A:=A) multA (n:=n) (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n) a (b:=ppc (A:=A) A1 (n:=n) c b) nZppcd) (spolyf (pX c r) (pX b q) Cpxc Cpxb)) (minuspf A A0 A1 eqA invA minusA multA eqA_dec n ltM ltM_dec (spminusf A A0 A1 eqA invA minusA multA divA eqA_dec n ltM ltM_dec a b nZb p q) (spminusf A A0 A1 eqA invA minusA multA divA eqA_dec n ltM ltM_dec a c nZc p r))); [ intros red3 | apply eqTerm_spolyf_red2; auto ].
2: apply ppc_nZ with (1 := cs); auto.
2: apply canonical_nzeroP with (ltM := ltM) (p := p); auto.
inversion_clear red_r0.
lapply (reduceplus_mults _ _ _ _ _ _ _ _ _ cs eqA_dec n ltM ltM_dec os Q (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n) a (b:=ppc (A:=A) A1 (n:=n) c b) nZppcd) (spolyf (pX c r) (pX b q) Cpxc Cpxb) (pO A n)); [ intros H'3; lapply H'3; [ intros H'4; lapply H'4; [ intros H'5; clear H'4 H'3 | clear H'4 H'3 ] | clear H'3 ] | idtac ]; auto.
elim (red_minus_zero_reduce _ _ _ _ _ _ _ _ _ cs eqA_dec _ _ ltM_dec os Q (spminusf A A0 A1 eqA invA minusA multA divA eqA_dec n ltM ltM_dec a b nZb p q) (spminusf A A0 A1 eqA invA minusA multA divA eqA_dec n ltM ltM_dec a c nZc p r)); [ intros r2 E; elim E; intros H'6 H'7; clear E | idtac | idtac | idtac ]; auto.
2: apply canonical_spminusf with (1 := cs); auto.
2: apply canonical_spminusf with (1 := cs); auto.
elim reduce0_reducestar with (1 := cs) (Q := Q) (p := r2) (ltM_dec := ltM_dec) (eqA_dec := eqA_dec); auto.
intros t0 E; lapply (Rec (spminusf A A0 A1 eqA invA minusA multA divA eqA_dec n ltM ltM_dec a b nZb p q)); [ intros H'1; lapply H'1; [ intros H'2; elim H'2; clear H'1 | clear H'1 ] | idtac ]; auto.
intros H'.
lapply (Rec (spminusf A A0 A1 eqA invA minusA multA divA eqA_dec n ltM ltM_dec a c nZc p r)); [ intros H'1; lapply H'1; [ intros H'3; elim H'3; clear H'1 | clear H'1 ] | idtac ]; auto.
intros H'1.
apply (eqp_trans _ _ _ _ _ _ _ _ _ cs n) with (y := t0).
apply H'; auto.
auto; apply (reducestar_trans A A0 A1 eqA plusA invA minusA multA divA cs eqA_dec n ltM ltM_dec os Q) with (y := r2); auto.
apply canonical_spminusf with (1 := cs); auto.
apply H'1; auto.
apply (reducestar_trans A A0 A1 eqA plusA invA minusA multA divA cs eqA_dec n ltM ltM_dec os Q) with (y := r2); auto.
apply canonical_spminusf with (1 := cs); auto.
apply ltP_reduce with (Q := Q) (1 := cs) (ltM_dec := ltM_dec) (eqA_dec := eqA_dec); auto.
apply canonical_spminusf with (1 := cs); auto.
apply ltP_reduce with (Q := Q) (1 := cs) (ltM_dec := ltM_dec) (eqA_dec := eqA_dec); auto.
apply canonical_spminusf with (1 := cs); auto.
apply canonical_reduceplus with (1 := cs) (3 := H'7); auto.
apply canonical_spminusf with (1 := cs); auto.
apply reduceplus_eqp_com with (p := mults (A:=A) multA (n:=n) (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n) a (b:=ppc (A:=A) A1 (n:=n) c b) nZppcd) (spolyf (pX c r) (pX b q) Cpxc Cpxb)) (q := mults (A:=A) multA (n:=n) (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n) a (b:=ppc (A:=A) A1 (n:=n) c b) nZppcd) (pO A n)) (1 := cs); auto; simpl in |- *; auto.
