Require Export Preduce.
Section Preduceplus.
Load hCoefStructure.
Load hOrderStructure.
Load hReduce.
Inductive reduceplus (Q : list (poly A0 eqA ltM)) : list (Term A n) -> list (Term A n) -> Prop := | Rstar_0 : forall x y : list (Term A n), eqP A eqA n x y -> reduceplus Q x y | Rstar_n : forall x y z : list (Term A n), reduce A A0 A1 eqA invA minusA multA divA eqA_dec n ltM ltM_dec Q x y -> reduceplus Q y z -> reduceplus Q x z.
Hint Resolve Rstar_0 : core.
Hint Resolve reduceplus_skip : core.
Hint Resolve reduce_imp_reduceplus : core.
End Preduceplus.

Theorem reduceplus_eqp_com : forall (Q : list (poly A0 eqA ltM)) (p q r s : list (Term A n)), reduceplus Q p q -> canonical A0 eqA ltM p -> eqP A eqA n p r -> eqP A eqA n q s -> reduceplus Q r s.
intros Q p q r s H'; generalize r s; clear r s; elim H'; auto.
intros x y H'0 r s H'1 H'2 H'3.
apply Rstar_0; auto.
apply (eqp_trans _ _ _ _ _ _ _ _ _ cs n) with (y := y); auto.
apply (eqp_trans _ _ _ _ _ _ _ _ _ cs n) with (y := x); auto.
apply (eqp_sym _ _ _ _ _ _ _ _ _ cs n); auto.
intros x y z H'0 H'1 H'2 r s H'3 H'4 H'5.
apply Rstar_n with (y := y); auto.
apply reduce_eqp_com with (1 := cs) (p := x) (q := y); auto.
apply H'2; auto.
Admitted.

Theorem reduceplus_trans : forall (Q : list (poly A0 eqA ltM)) (x y z : list (Term A n)), reduceplus Q x y -> canonical A0 eqA ltM x -> reduceplus Q y z -> reduceplus Q x z.
intros Q x y z H'; elim H'; auto.
intros x0 y0 H'0 H'1 H'2.
apply reduceplus_eqp_com with (p := y0) (q := z); auto.
apply eqp_imp_canonical with (1 := cs) (p := x0); auto.
apply (eqp_sym _ _ _ _ _ _ _ _ _ cs n); auto.
intros x0 y0 z0 H'0 H'1 H'2 H'3 H'4.
apply Rstar_n with (y := y0); auto.
apply H'2; auto.
Admitted.

Theorem canonical_reduceplus : forall (Q : list (poly A0 eqA ltM)) (p q : list (Term A n)), reduceplus Q p q -> canonical A0 eqA ltM p -> canonical A0 eqA ltM q.
intros Q p q H'; elim H'; auto.
intros x y H H0.
apply eqp_imp_canonical with (1 := cs) (p := x); auto.
intros x y z H'0 H'1 H'2 H'3.
apply H'2; auto.
Admitted.

Theorem order_reduceplus : forall (Q : list (poly A0 eqA ltM)) (p q : list (Term A n)), reduceplus Q p q -> canonical A0 eqA ltM p -> ltP (A:=A) (n:=n) ltM q p \/ eqP A eqA n p q.
intros Q p q H'; elim H'; auto.
intros x y z H'0 H'1 H'2 H'3; left; try assumption.
elim H'2; [ intros H'5; try exact H'5; clear H'2 | intros H'5; clear H'2 | clear H'2 ].
apply ltP_trans with (y := y); auto.
apply ltP_reduce with (1 := cs) (3 := H'0); auto.
apply (ltp_eqp_comp A A0 eqA) with (p := y) (q := x); auto.
apply ltP_reduce with (1 := cs) (3 := H'0); auto.
apply canonical_reduce with (1 := cs) (3 := H'0); auto.
Admitted.

Theorem reduce_imp_reduceplus : forall (Q : list (poly A0 eqA ltM)) (p q : list (Term A n)), reduce A A0 A1 eqA invA minusA multA divA eqA_dec n ltM ltM_dec Q p q -> reduceplus Q p q.
intros Q p q H'.
Admitted.

Lemma pO_reduceplus : forall (Q : list (poly A0 eqA ltM)) (p q : list (Term A n)), reduceplus Q (pO A n) p -> p = pO A n.
intros Q p q H'; inversion H'; auto.
inversion H; auto.
Admitted.

Theorem rep_plus_reduce : forall (Q : list (poly A0 eqA ltM)) (p q s : list (Term A n)), reduce A A0 A1 eqA invA minusA multA divA eqA_dec n ltM ltM_dec Q (pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec p q) s -> canonical A0 eqA ltM p -> canonical A0 eqA ltM q -> exists p1 : list (Term A n), (exists q1 : list (Term A n), reduceplus Q p p1 /\ reduceplus Q q q1 /\ eqP A eqA n s (pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec p1 q1)).
intros Q p q; pattern p, q in |- *.
apply (Opm_ind A n ltM ltM_dec); intros; auto.
exists (pO A n); exists s; split; [ idtac | split ]; auto.
apply reduce_imp_reduceplus.
apply reduce_eqp_com with (1 := cs) (p := pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec (pO A n) p0) (q := s); auto.
apply (eqp_sym _ _ _ _ _ _ _ _ _ cs n); auto.
exists s; exists (pO A n); split; [ idtac | split ]; auto.
apply reduce_imp_reduceplus.
apply reduce_eqp_com with (1 := cs) (p := pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec p0 (pO A n)) (q := s); auto.
apply (eqp_sym _ _ _ _ _ _ _ _ _ cs n); auto.
cut (canonical A0 eqA ltM p0); [ intros C0 | apply canonical_imp_canonical with (a := a); auto ].
cut (canonical A0 eqA ltM q0); [ intros C1 | apply canonical_imp_canonical with (a := b); auto ].
cut (~ zeroP (A:=A) A0 eqA (n:=n) a); [ intros nZ1 | apply canonical_nzeroP with (ltM := ltM) (p := p0); auto ].
cut (~ zeroP (A:=A) A0 eqA (n:=n) b); [ intros nZ2 | apply canonical_nzeroP with (ltM := ltM) (p := q0); auto ].
inversion H1.
cut (canonical A0 eqA ltM (pX b0 q1)); [ intros C2 | apply inPolySet_imp_canonical with (L := Q); auto ].
cut (canonical A0 eqA ltM q1); [ intros C3 | apply canonical_imp_canonical with (a := b0); auto ].
exists (pX a p0); exists (spminusf A A0 A1 eqA invA minusA multA divA eqA_dec n ltM ltM_dec b b0 nZb q0 q1); split; [ idtac | split ]; auto.
apply reduce_imp_reduceplus.
apply reducetop with (b := b0) (nZb := nZb) (q := q1); auto.
cut (eqTerm (A:=A) eqA (n:=n) a0 b); [ intros eqb | idtac ].
apply divP_eqT with (1 := cs) (a := a0); auto.
rewrite <- pluspf_inv2_eq with (1 := os) (a := a) (b := b) (p := p0) (q := q0) in H4; auto.
rewrite (pX_invl _ _ a0 b p1 (pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec (pX a p0) q0)); auto.
rewrite <- pluspf_inv2_eq with (1 := os) (a := a) (b := b) (p := p0) (q := q0) in H4; auto.
rewrite (pX_invl _ _ a0 b p1 (pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec (pX a p0) q0)); auto.
apply (eqp_trans _ _ _ _ _ _ _ _ _ cs n) with (y := spminusf A A0 A1 eqA invA minusA multA divA eqA_dec n ltM ltM_dec a0 b0 nZb p1 q1); auto.
apply (eqp_sym _ _ _ _ _ _ _ _ _ cs n); auto.
rewrite <- pluspf_inv2_eq with (1 := os) (a := a) (b := b) (p := p0) (q := q0) in H4; auto.
rewrite (pX_invl _ _ a0 b p1 (pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec (pX a p0) q0)); auto.
rewrite (pX_invr _ _ p1 (pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec (pX a p0) q0) a0 b); auto.
apply spminusf_plusTerm_r; auto.
rewrite <- (pX_invl _ _ a0 b p1 (pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec (pX a p0) q0)); auto.
elim (H q1); [ intros p2 E; elim E; intros q2 E0; elim E0; intros H'4 H'5; elim H'5; intros H'6 H'7; clear H'5 E0 E | idtac | idtac | idtac ]; auto.
exists p2; exists (pX b q2); split; [ idtac | split ]; auto.
apply (eqp_trans _ _ _ _ _ _ _ _ _ cs n) with (y := pX a0 (pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec p2 q2)); auto.
apply eqpP1; auto; (apply (eqTerm_sym _ _ _ _ _ _ _ _ _ cs n); auto).
rewrite <- pluspf_inv2_eq with (1 := os) (a := a) (b := b) (p := p0) (q := q0) in H4; auto.
rewrite (pX_invl _ _ a0 b p1 (pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec (pX a p0) q0)); auto.
rewrite pluspf_inv2_eqa; auto.
apply ltP_pX_canonical; auto.
apply canonical_reduceplus with (Q := Q) (p := pX a p0); auto.
elim (order_reduceplus Q (pX a p0) p2); [ intros H'5 | intros H'5 | idtac | idtac ]; auto.
apply ltP_trans with (y := pX a p0); auto.
apply (ltp_eqp_comp A A0 eqA) with (p := pX a p0) (q := pX b (pO A n)); auto.
apply ltP_pX_canonical; auto.
apply canonical_reduceplus with (Q := Q) (p := q0); auto.
elim (order_reduceplus Q q0 q2); [ intros H'5 | intros H'5 | idtac | idtac ]; auto.
apply ltP_trans with (y := q0); auto.
apply (canonical_pX_ltP A A0 eqA); auto.
apply (ltp_eqp_comp A A0 eqA) with (p := q0) (q := pX b (pO A n)); auto.
apply (canonical_pX_ltP A A0 eqA); auto.
apply reduce_eqp_com with (1 := cs) (p := p1) (q := q1); auto.
apply canonical_imp_canonical with (a := a0); auto.
rewrite H4; auto.
rewrite <- pluspf_inv2_eq with (1 := os) (a := a) (b := b) (p := p0) (q := q0) in H4; auto.
rewrite (pX_invr _ _ p1 (pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec (pX a p0) q0) a0 b); auto.
rewrite <- pluspf_inv1_eq with (a := a) (b := b) (p := p0) (q := q0) in H1; auto.
cut (canonical A0 eqA ltM p0); [ intros C0 | apply canonical_imp_canonical with (a := a); auto ].
cut (canonical A0 eqA ltM q0); [ intros C1 | apply canonical_imp_canonical with (a := b); auto ].
cut (~ zeroP (A:=A) A0 eqA (n:=n) a); [ intros nZ1 | apply canonical_nzeroP with (ltM := ltM) (p := p0); auto ].
cut (~ zeroP (A:=A) A0 eqA (n:=n) b); [ intros nZ2 | apply canonical_nzeroP with (ltM := ltM) (p := q0); auto ].
inversion_clear H1.
cut (canonical A0 eqA ltM (pX b0 q1)); [ intros C2 | apply inPolySet_imp_canonical with (L := Q); auto ].
cut (canonical A0 eqA ltM q1); [ intros C3 | apply canonical_imp_canonical with (a := b0); auto ].
cut (~ zeroP (A:=A) A0 eqA (n:=n) b0); [ intros nZ3 | apply canonical_nzeroP with (ltM := ltM) (p := q1); auto ].
exists (spminusf A A0 A1 eqA invA minusA multA divA eqA_dec n ltM ltM_dec a b0 nZb p0 q1); exists (pX b q0); split; [ idtac | split ]; auto.
apply reduce_imp_reduceplus; auto.
apply reducetop with (b := b0) (nZb := nZb) (q := q1); auto.
apply (eqp_trans _ _ _ _ _ _ _ _ _ cs n) with (y := spminusf A A0 A1 eqA invA minusA multA divA eqA_dec n ltM ltM_dec a b0 nZb (pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec p0 (pX b q0)) q1).
apply (eqp_sym _ _ _ _ _ _ _ _ _ cs n); auto.
apply spminusf_pluspf; auto.
elim (H q1); [ intros p2 E; elim E; intros q2 E0; elim E0; intros H'4 H'5; elim H'5; intros H'6 H'7; clear H'5 E0 E | idtac | idtac | idtac ]; auto.
exists (pX a p2); exists q2; split; [ idtac | split ]; auto.
apply (eqp_trans _ _ _ _ _ _ _ _ _ cs n) with (y := pX a (pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec p2 q2)); auto.
apply eqpP1; auto.
apply (eqTerm_sym _ _ _ _ _ _ _ _ _ cs n); auto.
rewrite pluspf_inv1_eqa; auto.
apply ltP_pX_canonical; auto.
apply canonical_reduceplus with (Q := Q) (p := p0); auto.
elim (order_reduceplus Q p0 p2); [ intros H'14 | intros H'14 | idtac | idtac ]; auto.
apply ltP_trans with (y := p0); auto.
apply (canonical_pX_ltP A A0 eqA); auto.
apply (ltp_eqp_comp A A0 eqA) with (p := p0) (q := pX a (pO A n)); auto.
apply (canonical_pX_ltP A A0 eqA); auto.
apply ltP_pX_canonical; auto.
apply canonical_reduceplus with (Q := Q) (p := pX b q0); auto.
elim (order_reduceplus Q (pX b q0) q2); [ intros H'14 | intros H'14 | idtac | idtac ]; auto.
apply ltP_trans with (y := pX b q0); auto.
apply (ltp_eqp_comp A A0 eqA) with (p := pX b q0) (q := pX a (pO A n)); auto.
cut (canonical A0 eqA ltM p0); [ intros C0 | apply canonical_imp_canonical with (a := a); auto ].
cut (canonical A0 eqA ltM q0); [ intros C1 | apply canonical_imp_canonical with (a := b); auto ].
cut (~ zeroP (A:=A) A0 eqA (n:=n) a); [ intros nZ1 | apply canonical_nzeroP with (ltM := ltM) (p := p0); auto ].
cut (~ zeroP (A:=A) A0 eqA (n:=n) b); [ intros nZ2 | apply canonical_nzeroP with (ltM := ltM) (p := q0); auto ].
case (zeroP_dec A A0 eqA eqA_dec n (plusTerm (A:=A) plusA (n:=n) a b)); intros Z0.
elim (H s); [ intros p1 E; elim E; intros q1 E0; elim E0; intros H'3 H'5; elim H'5; intros H'6 H'7; clear H'5 E0 E | idtac | idtac | idtac ]; auto.
exists (pX a p1); exists (pX b q1); split; [ idtac | split ]; auto.
apply (eqp_trans _ _ _ _ _ _ _ _ _ cs n) with (y := pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec p1 q1); auto.
apply pluspf_inv3a with (1 := cs); auto.
rewrite pluspf_inv3a_eq with (1 := os) (a := a) (b := b) (p := p0) (q := q0); auto.
inversion H1.
cut (canonical A0 eqA ltM (pX b0 q1)); [ intros C2 | apply inPolySet_imp_canonical with (L := Q); auto ].
cut (canonical A0 eqA ltM q1); [ intros C3 | apply canonical_imp_canonical with (a := b0); auto ].
cut (divP A A0 eqA multA divA n a b0); [ intros div0 | idtac ].
cut (divP A A0 eqA multA divA n b b0); [ intros div1 | idtac ].
exists (spminusf A A0 A1 eqA invA minusA multA divA eqA_dec n ltM ltM_dec a b0 nZb p0 q1); exists (spminusf A A0 A1 eqA invA minusA multA divA eqA_dec n ltM ltM_dec b b0 nZb q0 q1); split; [ idtac | split ]; auto.
apply reduce_imp_reduceplus; auto.
apply reducetop with (b := b0) (nZb := nZb) (q := q1); auto.
apply reduce_imp_reduceplus; auto.
apply reducetop with (b := b0) (nZb := nZb) (q := q1); auto.
apply (eqp_trans _ _ _ _ _ _ _ _ _ cs n) with (y := spminusf A A0 A1 eqA invA minusA multA divA eqA_dec n ltM ltM_dec a0 b0 nZb p1 q1).
apply (eqp_sym _ _ _ _ _ _ _ _ _ cs n); auto.
rewrite <- pluspf_inv3b_eq with (1 := os) (a := a) (b := b) (p := p0) (q := q0) in H4; auto.
rewrite pX_invr with (1 := H4); auto.
rewrite pX_invl with (1 := H4); auto.
apply spminusf_plusTerm; auto.
apply divP_eqT with (1 := cs) (a := plusTerm (A:=A) plusA (n:=n) a b); auto.
apply plusTerm_eqT2; auto.
rewrite <- pluspf_inv3b_eq with (1 := os) (a := a) (b := b) (p := p0) (q := q0) in H4; auto.
rewrite <- pX_invl with (1 := H4); auto.
apply divP_eqT with (1 := cs) (a := plusTerm (A:=A) plusA (n:=n) a b); auto.
apply plusTerm_eqT1; auto.
rewrite <- pluspf_inv3b_eq with (1 := os) (a := a) (b := b) (p := p0) (q := q0) in H4; auto.
rewrite <- pX_invl with (1 := H4); auto.
rewrite <- pluspf_inv3b_eq with (1 := os) (a := a) (b := b) (p := p0) (q := q0) in H4; auto.
elim (H q1); [ intros p2 E; elim E; intros q2 E0; elim E0; intros H'3 H'5; elim H'5; intros H'6 H'7; clear H'5 E0 E | idtac | idtac | idtac ]; auto.
exists (pX a p2); exists (pX b q2); split; [ idtac | split ]; auto.
apply (eqp_trans _ _ _ _ _ _ _ _ _ cs n) with (y := pX a0 (pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec p2 q2)); auto.
apply eqpP1; auto; apply (eqTerm_sym _ _ _ _ _ _ _ _ _ cs n); auto.
rewrite pX_invl with (1 := H4); auto.
apply pluspf_inv3b with (1 := cs); auto.
Admitted.

Theorem reduceplus_mults : forall (Q : list (poly A0 eqA ltM)) (a : Term A n) (p q : list (Term A n)), reduceplus Q p q -> canonical A0 eqA ltM p -> ~ zeroP (A:=A) A0 eqA (n:=n) a -> reduceplus Q (mults (A:=A) multA (n:=n) a p) (mults (A:=A) multA (n:=n) a q).
intros Q a p q H'; elim H'; auto.
intros x y z H'0 H'1 H'2 H'3 H'4.
apply Rstar_n with (y := mults (A:=A) multA (n:=n) a y); auto.
apply reduce_mults with (1 := cs); auto.
apply H'2; auto.
Admitted.

Lemma reduceplus_mults_invr_lem : forall (Q : list (poly A0 eqA ltM)) (p q : list (Term A n)), reduceplus Q p q -> forall r : list (Term A n), eqP A eqA n p (mults (A:=A) multA (n:=n) (invTerm (A:=A) invA (n:=n) (T1 A1 n)) r) -> canonical A0 eqA ltM r -> reduceplus Q r (mults (A:=A) multA (n:=n) (invTerm (A:=A) invA (n:=n) (T1 A1 n)) q).
intros Q p q H'; elim H'; auto.
intros x y H'0 r H'1 H'2.
apply Rstar_0; auto.
apply (eqp_trans _ _ _ _ _ _ _ _ _ cs n) with (y := mults (A:=A) multA (n:=n) (invTerm (A:=A) invA (n:=n) (T1 A1 n)) x); auto.
apply (eqp_trans _ _ _ _ _ _ _ _ _ cs n) with (y := mults (A:=A) multA (n:=n) (invTerm (A:=A) invA (n:=n) (T1 A1 n)) (mults (A:=A) multA (n:=n) (invTerm (A:=A) invA (n:=n) (T1 A1 n)) r)); auto.
apply (eqp_trans _ _ _ _ _ _ _ _ _ cs n) with (y := mults (A:=A) multA (n:=n) (multTerm (A:=A) multA (n:=n) (invTerm (A:=A) invA (n:=n) (T1 A1 n)) (invTerm (A:=A) invA (n:=n) (T1 A1 n))) r); auto.
apply (eqp_sym _ _ _ _ _ _ _ _ _ cs n); apply (eqp_trans _ _ _ _ _ _ _ _ _ cs n) with (y := mults (A:=A) multA (n:=n) (T1 A1 n) r); auto.
apply (eqp_sym _ _ _ _ _ _ _ _ _ cs n); auto.
intros x y z H'0 H'1 H'2 r H'3 H'4.
apply Rstar_n with (y := mults (A:=A) multA (n:=n) (invTerm (A:=A) invA (n:=n) (T1 A1 n)) y); auto.
apply reduce_mults_invr with (1 := cs); auto.
apply reduce_eqp_com with (1 := cs) (p := x) (q := y); auto.
apply eqp_imp_canonical with (p := mults (A:=A) multA (n:=n) (invTerm (A:=A) invA (n:=n) (T1 A1 n)) r) (1 := cs); auto.
apply (eqp_sym _ _ _ _ _ _ _ _ _ cs n); auto.
apply reduceplus_mults; auto.
apply canonical_reduce with (1 := cs) (3 := H'0); auto.
apply eqp_imp_canonical with (p := mults (A:=A) multA (n:=n) (invTerm (A:=A) invA (n:=n) (T1 A1 n)) r) (1 := cs); auto.
Admitted.

Theorem reduceplus_mults_invr : forall (Q : list (poly A0 eqA ltM)) (p q : list (Term A n)), reduceplus Q (mults (A:=A) multA (n:=n) (invTerm (A:=A) invA (n:=n) (T1 A1 n)) p) q -> canonical A0 eqA ltM p -> reduceplus Q p (mults (A:=A) multA (n:=n) (invTerm (A:=A) invA (n:=n) (T1 A1 n)) q).
intros Q p q H' H'0.
Admitted.

Theorem reduceplus_mults_invf0 : forall a : Term A n, ~ zeroP (A:=A) A0 eqA (n:=n) a -> eqT a (T1 A1 n) -> forall (Q : list (poly A0 eqA ltM)) (p q : list (Term A n)), reduceplus Q p q -> canonical A0 eqA ltM p -> forall r s : list (Term A n), canonical A0 eqA ltM r -> eqP A eqA n p (mults (A:=A) multA (n:=n) a r) -> eqP A eqA n q (mults (A:=A) multA (n:=n) a s) -> reduceplus Q r s.
intros a H' H'0 Q p q H'1; elim H'1; auto.
intros x y H'2 H'3 r s H'4 H'5 H'6.
apply Rstar_0; auto.
apply mults_eqp_inv with (a := a) (1 := cs); auto.
apply (eqp_trans _ _ _ _ _ _ _ _ _ cs n) with (y := y); auto.
apply (eqp_trans _ _ _ _ _ _ _ _ _ cs n) with (y := x); auto.
apply (eqp_sym _ _ _ _ _ _ _ _ _ cs n); auto.
intros x y z H'2 H'3 H'4 H'5 r s H'6 H'7 H'8.
apply Rstar_n with (y := mults (A:=A) multA (n:=n) (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n) (T1 A1 n) (b:=a) H') y); auto.
apply reduce_mults_invf with (1 := cs); auto.
apply reduce_eqp_com with (1 := cs) (p := x) (q := y); auto.
apply H'4; auto.
apply canonical_reduce with (1 := cs) (3 := H'2); auto.
apply canonical_mults with (1 := cs); auto.
apply canonical_reduce with (1 := cs) (3 := H'2); auto.
apply (eqp_trans _ _ _ _ _ _ _ _ _ cs n) with (y := mults (A:=A) multA (n:=n) (multTerm (A:=A) multA (n:=n) a (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n) (T1 A1 n) (b:=a) H')) y); auto.
apply (eqp_trans _ _ _ _ _ _ _ _ _ cs n) with (y := mults (A:=A) multA (n:=n) (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n) (multTerm (A:=A) multA (n:=n) a (T1 A1 n)) (b:=a) H') y); auto.
apply (eqp_trans _ _ _ _ _ _ _ _ _ cs n) with (y := mults (A:=A) multA (n:=n) (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n) a (b:=a) H') y); auto.
apply (eqp_sym _ _ _ _ _ _ _ _ _ cs n); auto.
apply mults_comp with (1 := cs); auto.
apply divTerm_multTerm_l with (1 := cs); auto.
apply divTerm_on_eqT with (1 := cs); auto.
Admitted.

Theorem reduceplus_mults_inv : forall a : Term A n, ~ zeroP (A:=A) A0 eqA (n:=n) a -> eqT a (T1 A1 n) -> forall (Q : list (poly A0 eqA ltM)) (p q : list (Term A n)), reduceplus Q (mults (A:=A) multA (n:=n) a p) (mults (A:=A) multA (n:=n) a q) -> canonical A0 eqA ltM p -> reduceplus Q p q.
intros a H' H'0 Q p q H'1 H'2.
Admitted.

Theorem rep_minus_reduce : forall (Q : list (poly A0 eqA ltM)) (p q s : list (Term A n)), reduce A A0 A1 eqA invA minusA multA divA eqA_dec n ltM ltM_dec Q (minuspf A A0 A1 eqA invA minusA multA eqA_dec n ltM ltM_dec p q) s -> canonical A0 eqA ltM p -> canonical A0 eqA ltM q -> exists p1 : list (Term A n), (exists q1 : list (Term A n), reduceplus Q p p1 /\ reduceplus Q q q1 /\ eqP A eqA n s (minuspf A A0 A1 eqA invA minusA multA eqA_dec n ltM ltM_dec p1 q1)).
intros Q p q s H' H'0 H'1.
elim (rep_plus_reduce Q p (mults (A:=A) multA (n:=n) (invTerm (A:=A) invA (n:=n) (T1 A1 n)) q) s); [ intros p1 E; elim E; intros q1 E0; elim E0; intros H'9 H'10; elim H'10; intros H'11 H'12; clear H'10 E0 E | idtac | idtac | idtac ]; auto.
exists p1; exists (mults (A:=A) multA (n:=n) (invTerm (A:=A) invA (n:=n) (T1 A1 n)) q1); split; [ idtac | split ]; auto.
apply reduceplus_mults_invr; auto.
cut (canonical A0 eqA ltM p1); [ intros Cp1 | idtac ].
cut (canonical A0 eqA ltM q1); [ intros Cq1 | idtac ].
apply (eqp_trans _ _ _ _ _ _ _ _ _ cs n) with (y := pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec p1 q1); auto.
apply (eqp_trans _ _ _ _ _ _ _ _ _ cs n) with (y := pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec p1 (mults (A:=A) multA (n:=n) (invTerm (A:=A) invA (n:=n) (T1 A1 n)) (mults (A:=A) multA (n:=n) (invTerm (A:=A) invA (n:=n) (T1 A1 n)) q1))); auto.
apply (eqp_trans _ _ _ _ _ _ _ _ _ cs n) with (y := pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec p1 (mults (A:=A) multA (n:=n) (multTerm (A:=A) multA (n:=n) (invTerm (A:=A) invA (n:=n) (T1 A1 n)) (invTerm (A:=A) invA (n:=n) (T1 A1 n))) q1)); auto.
apply (eqp_sym _ _ _ _ _ _ _ _ _ cs n); apply (eqp_trans _ _ _ _ _ _ _ _ _ cs n) with (y := pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec p1 (mults (A:=A) multA (n:=n) (T1 A1 n) q1)); auto.
apply (eqp_sym _ _ _ _ _ _ _ _ _ cs n); auto.
apply canonical_reduceplus with (Q := Q) (p := mults (A:=A) multA (n:=n) (invTerm (A:=A) invA (n:=n) (T1 A1 n)) q); auto.
apply canonical_reduceplus with (Q := Q) (p := p); auto.
Admitted.

Theorem rep_plus_zero_reduce : forall (Q : list (poly A0 eqA ltM)) (s t : list (Term A n)), reduceplus Q s t -> canonical A0 eqA ltM s -> forall p q : list (Term A n), eqP A eqA n s (pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec p q) -> canonical A0 eqA ltM p -> canonical A0 eqA ltM q -> eqP A eqA n t (pO A n) -> exists r1 : list (Term A n), reduceplus Q p r1 /\ reduceplus Q q (mults (A:=A) multA (n:=n) (invTerm (A:=A) invA (n:=n) (T1 A1 n)) r1).
intros Q s t H'; elim H'.
intros x y eqxy Op p q H'0 H'1 H'2 H'3; exists p; split; auto.
apply Rstar_0; auto.
cut (canonical A0 eqA ltM y); [ intros Cx | idtac ].
apply (eqp_trans _ _ _ _ _ _ _ _ _ cs n) with (y := pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec (pO A n) (mults (A:=A) multA (n:=n) (invTerm (A:=A) invA (n:=n) (T1 A1 n)) p)); auto.
apply (eqp_trans _ _ _ _ _ _ _ _ _ cs n) with (y := pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec y (mults (A:=A) multA (n:=n) (invTerm (A:=A) invA (n:=n) (T1 A1 n)) p)); auto.
apply (eqp_trans _ _ _ _ _ _ _ _ _ cs n) with (y := pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec x (mults (A:=A) multA (n:=n) (invTerm (A:=A) invA (n:=n) (T1 A1 n)) p)); auto.
apply (eqp_sym _ _ _ _ _ _ _ _ _ cs n); apply (eqp_trans _ _ _ _ _ _ _ _ _ cs n) with (y := pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec (pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec p q) (mults (A:=A) multA (n:=n) (invTerm (A:=A) invA (n:=n) (T1 A1 n)) p)); auto.
apply (eqp_trans _ _ _ _ _ _ _ _ _ cs n) with (y := pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec (pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec q p) (mults (A:=A) multA (n:=n) (invTerm (A:=A) invA (n:=n) (T1 A1 n)) p)); auto.
apply (eqp_trans _ _ _ _ _ _ _ _ _ cs n) with (y := pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec q (pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec p (mults (A:=A) multA (n:=n) (invTerm (A:=A) invA (n:=n) (T1 A1 n)) p))); auto.
apply (eqp_sym _ _ _ _ _ _ _ _ _ cs n); apply (eqp_trans _ _ _ _ _ _ _ _ _ cs n) with (y := pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec q (minuspf A A0 A1 eqA invA minusA multA eqA_dec n ltM ltM_dec p p)); auto.
apply (eqp_sym _ _ _ _ _ _ _ _ _ cs n); apply (eqp_trans _ _ _ _ _ _ _ _ _ cs n) with (y := pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec q (pO A n)); auto.
apply eqp_pluspf_com with (1 := cs); auto.
apply minuspf_refl with (1 := cs); auto.
apply eqp_imp_canonical with (1 := cs) (p := x); auto.
intros x y z H'0 H'1 H'2 H'3 p q H'4 H'5 H'6 H'7.
elim (rep_plus_reduce Q p q y); [ intros p1 E; elim E; intros q1 E0; elim E0; intros H'15 H'16; elim H'16; intros H'17 H'18; try exact H'17; clear H'16 E0 E | idtac | idtac | idtac ]; auto.
lapply H'2; [ intros H'8; elim (H'8 p1 q1); [ intros r1 E; elim E; intros H'16 H'19; clear E H'2 | clear H'2 | clear H'2 | clear H'2 | clear H'2 ] | clear H'2 ]; auto.
exists r1; split; auto.
apply reduceplus_trans with (y := p1); auto.
apply reduceplus_trans with (y := q1); auto.
apply canonical_reduceplus with (Q := Q) (p := p); auto.
apply canonical_reduceplus with (Q := Q) (p := q); auto.
apply eqp_imp_canonical with (1 := cs) (p := pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec p1 q1); auto.
apply (eqp_sym _ _ _ _ _ _ _ _ _ cs n); auto.
apply canonical_pluspf; auto.
apply canonical_reduceplus with (Q := Q) (p := p); auto.
apply canonical_reduceplus with (Q := Q) (p := q); auto.
Admitted.

Theorem reduceplus_skip : forall (Q : list (poly A0 eqA ltM)) (a b : Term A n) (p q : list (Term A n)), reduceplus Q p q -> canonical A0 eqA ltM (pX a p) -> eqTerm (A:=A) eqA (n:=n) a b -> reduceplus Q (pX a p) (pX b q).
intros Q a b p q H'; generalize a b; clear a b; elim H'; auto.
intros x y z H'0 H'1 H'2 a b H'3 H'4.
apply Rstar_n with (y := pX b y); auto.
apply H'2; auto.
apply ltP_pX_canonical; auto.
apply canonical_reduce with (1 := cs) (3 := H'0); auto.
apply canonical_imp_canonical with (a := a); auto.
apply canonical_nzeroP with (ltM := ltM) (p := x); auto.
apply eqp_imp_canonical with (1 := cs) (p := pX a x); auto.
apply ltP_trans with (y := x); auto.
apply ltP_reduce with (1 := cs) (3 := H'0); auto.
apply canonical_imp_canonical with (a := a); auto.
apply (canonical_pX_ltP A A0 eqA); auto.
apply eqp_imp_canonical with (1 := cs) (p := pX a x); auto.
