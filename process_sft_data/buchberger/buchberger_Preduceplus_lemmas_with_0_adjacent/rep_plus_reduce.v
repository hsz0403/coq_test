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
rewrite <- pX_invr with (1 := H4); auto.
