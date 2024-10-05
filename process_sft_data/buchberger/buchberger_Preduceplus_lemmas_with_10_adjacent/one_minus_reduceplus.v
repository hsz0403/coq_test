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

Theorem red_plus_zero_reduce : forall (Q : list (poly A0 eqA ltM)) (p q : list (Term A n)), canonical A0 eqA ltM p -> canonical A0 eqA ltM q -> reduceplus Q (pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec p q) (pO A n) -> exists r1 : list (Term A n), reduceplus Q p r1 /\ reduceplus Q q (mults (A:=A) multA (n:=n) (invTerm (A:=A) invA (n:=n) (T1 A1 n)) r1).
intros Q p q H' H'0 H'1.
Admitted.

Theorem red_minus_zero_reduce : forall (Q : list (poly A0 eqA ltM)) (p q : list (Term A n)), canonical A0 eqA ltM p -> canonical A0 eqA ltM q -> reduceplus Q (minuspf A A0 A1 eqA invA minusA multA eqA_dec n ltM ltM_dec p q) (pO A n) -> exists r1 : list (Term A n), reduceplus Q p r1 /\ reduceplus Q q r1.
intros Q p q H' H'0 H'1.
elim (red_plus_zero_reduce Q p (mults (A:=A) multA (n:=n) (invTerm (A:=A) invA (n:=n) (T1 A1 n)) q)); [ intros r1 E; elim E; intros H'8 H'9; clear E | idtac | idtac | idtac ]; auto.
exists r1; split; auto.
apply reduceplus_eqp_com with (p := q) (q := mults (A:=A) multA (n:=n) (invTerm (A:=A) invA (n:=n) (T1 A1 n)) (mults (A:=A) multA (n:=n) (invTerm (A:=A) invA (n:=n) (T1 A1 n)) r1)); auto.
apply reduceplus_mults_invr; auto.
apply (eqp_trans _ _ _ _ _ _ _ _ _ cs n) with (y := mults (A:=A) multA (n:=n) (multTerm (A:=A) multA (n:=n) (invTerm (A:=A) invA (n:=n) (T1 A1 n)) (invTerm (A:=A) invA (n:=n) (T1 A1 n))) r1); auto.
apply (eqp_sym _ _ _ _ _ _ _ _ _ cs n); auto.
Admitted.

Theorem reduce_plus_top : forall (Q : list (poly A0 eqA ltM)) (r : list (Term A n)), canonical A0 eqA ltM r -> forall (a b : Term A n) (nZb : ~ zeroP (A:=A) A0 eqA (n:=n) b) (p q : list (Term A n)), inPolySet A A0 eqA n ltM (pX b q) Q -> canonical A0 eqA ltM (pX a p) -> divP A A0 eqA multA divA n a b -> ex (fun s : list (Term A n) => reduceplus Q (pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec (pX a p) r) s /\ reduceplus Q (pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec (spminusf A A0 A1 eqA invA minusA multA divA eqA_dec n ltM ltM_dec a b nZb p q) r) s).
intros Q r; elim r; auto.
intros H' a b nZb p q H'0 H'1 H'2; exists (spminusf A A0 A1 eqA invA minusA multA divA eqA_dec n ltM ltM_dec a b nZb p q); split; auto.
apply reduceplus_eqp_com with (p := pX a p) (q := spminusf A A0 A1 eqA invA minusA multA divA eqA_dec n ltM ltM_dec a b nZb p q); auto.
apply reduce_imp_reduceplus; auto.
apply reducetop with (b := b) (nZb := nZb) (q := q); auto.
apply (eqp_sym _ _ _ _ _ _ _ _ _ cs n); auto.
change (eqP A eqA n (pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec (pX a p) (pO A n)) (pX a p)) in |- *; auto.
change (reduceplus Q (pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec (spminusf A A0 A1 eqA invA minusA multA divA eqA_dec n ltM ltM_dec a b nZb p q) (pO A n)) (spminusf A A0 A1 eqA invA minusA multA divA eqA_dec n ltM ltM_dec a b nZb p q)) in |- *; auto.
clear r; intros c r H' H'0 a b nZb p q H'1 H'2 H'3.
cut (canonical A0 eqA ltM p); [ intros C0 | apply canonical_imp_canonical with (a := a); auto ].
cut (canonical A0 eqA ltM (pX b q)); [ intros C1 | apply inPolySet_imp_canonical with (L := Q); auto ].
cut (canonical A0 eqA ltM q); [ intros C2 | apply canonical_imp_canonical with (a := b); auto ].
cut (canonical A0 eqA ltM r); [ intros C3 | apply canonical_imp_canonical with (a := c); auto ].
cut (~ zeroP (A:=A) A0 eqA (n:=n) a); [ intros nZ1 | apply canonical_nzeroP with (ltM := ltM) (p := p); auto ].
cut (~ zeroP (A:=A) A0 eqA (n:=n) c); [ intros nZ3 | apply canonical_nzeroP with (ltM := ltM) (p := r); auto ].
case (ltT_dec A n ltM ltM_dec a c); [ intros temp; case temp; clear temp | idtac ]; intros test.
lapply H'; [ intros H'4; elim (H'4 a b nZb p q); [ intros s E; elim E; intros H'13 H'14; clear E H' | clear H' | clear H' | clear H' ] | clear H' ]; auto.
exists (pX c s); split; auto.
change (reduceplus Q (pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec (pX a p) (pX c r)) (pX c s)) in |- *.
rewrite <- pluspf_inv2_eq with (1 := os) (a := a) (b := c) (p := p) (q := r); auto.
apply reduceplus_skip; auto.
rewrite pluspf_inv2_eq with (1 := os) (a := a) (b := c) (p := p) (q := r); auto.
change (reduceplus Q (pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec (spminusf A A0 A1 eqA invA minusA multA divA eqA_dec n ltM ltM_dec a b nZb p q) (pX c r)) (pX c s)) in |- *.
cut (canonical A0 eqA ltM (pX a (spminusf A A0 A1 eqA invA minusA multA divA eqA_dec n ltM ltM_dec a b nZb p q))); auto.
generalize H'14; case (spminusf A A0 A1 eqA invA minusA multA divA eqA_dec n ltM ltM_dec a b nZb p q); simpl in |- *; auto.
intros H' H'5.
apply reduceplus_eqp_com with (p := pX c (pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec (pO A n) r)) (q := pX c s); auto.
apply reduceplus_skip; auto.
apply eqp_imp_canonical with (1 := cs) (p := pX c r); auto.
apply (eqp_sym _ _ _ _ _ _ _ _ _ cs n); auto.
apply eqp_imp_canonical with (1 := cs) (p := pX c r); auto.
apply (eqp_sym _ _ _ _ _ _ _ _ _ cs n); auto.
apply (eqp_trans _ _ _ _ _ _ _ _ _ cs n) with (y := pX c r); auto.
apply (eqp_sym _ _ _ _ _ _ _ _ _ cs n); auto.
change (eqP A eqA n (pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec (pO A n) (pX c r)) (pX c r)) in |- *; auto.
intros t l H' H'5.
change (reduceplus Q (pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec (pX t l) (pX c r)) (pX c s)) in |- *.
rewrite <- pluspf_inv2_eq with (1 := os) (a := t) (b := c) (p := l) (q := r); auto.
apply reduceplus_skip; auto.
rewrite pluspf_inv2_eq with (1 := os) (a := t) (b := c) (p := l) (q := r); auto.
apply canonical_pluspf; auto.
apply canonical_imp_canonical with (a := a); auto.
apply (ltT_trans A _ _ os) with (y := a); auto.
apply (canonical_pX_order A A0 eqA) with (l := l); auto.
apply (ltT_trans A _ _ os) with (y := a); auto.
apply (canonical_pX_order A A0 eqA) with (l := l); auto.
apply canonical_spminusf_full_t with (1 := cs); auto.
exists (pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec (spminusf A A0 A1 eqA invA minusA multA divA eqA_dec n ltM ltM_dec a b nZb p q) (pX c r)); split; auto.
apply reduce_imp_reduceplus.
change (reduce A A0 A1 eqA invA minusA multA divA eqA_dec n ltM ltM_dec Q (pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec (pX a p) (pX c r)) (pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec (spminusf A A0 A1 eqA invA minusA multA divA eqA_dec n ltM ltM_dec a b nZb p q) (pX c r))) in |- *.
rewrite <- pluspf_inv1_eq with (1 := os) (a := a) (b := c) (p := p) (q := r); auto.
apply reducetop with (b := b) (nZb := nZb) (q := q); auto.
apply spminusf_pluspf with (1 := cs); auto.
cut (divP A A0 eqA multA divA n c b); [ intros divc | apply divP_eqT with (1 := cs) (a := a) ]; auto.
cut (canonical A0 eqA ltM (pX c (spminusf A A0 A1 eqA invA minusA multA divA eqA_dec n ltM ltM_dec a b nZb p q))); [ intros Ca | apply canonical_pX_eqT with (a := a) ]; auto.
case (zeroP_dec A A0 eqA eqA_dec n (plusTerm (A:=A) plusA (n:=n) a c)); intros Z0.
exists (pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec p r); split; auto.
change (reduceplus Q (pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec (pX a p) (pX c r)) (pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec p r)) in |- *.
rewrite <- pluspf_inv3a_eq with (1 := os) (a := a) (b := c) (p := p) (q := r); auto.
change (reduceplus Q (pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec (spminusf A A0 A1 eqA invA minusA multA divA eqA_dec n ltM ltM_dec a b nZb p q) (pX c r)) (pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec p r)) in |- *.
rewrite <- pluspf_inv2_eqa; auto.
apply reduce_imp_reduceplus.
apply reducetop with (b := b) (nZb := nZb) (q := q); auto.
apply (eqp_trans _ _ _ _ _ _ _ _ _ cs n) with (y := pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec (spminusf A A0 A1 eqA invA minusA multA divA eqA_dec n ltM ltM_dec a b nZb p q) (spminusf A A0 A1 eqA invA minusA multA divA eqA_dec n ltM ltM_dec c b nZb r q)); auto.
apply spminusf_plusTerm_r with (1 := cs); auto.
apply canonical_spminusf with (1 := cs); auto.
apply (eqp_sym _ _ _ _ _ _ _ _ _ cs n); auto.
apply spminusf_plusTerm_z; auto.
exists (spminusf A A0 A1 eqA invA minusA multA divA eqA_dec n ltM ltM_dec (plusTerm (A:=A) plusA (n:=n) a c) b nZb (pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec p r) q); split; auto.
change (reduceplus Q (pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec (pX a p) (pX c r)) (spminusf A A0 A1 eqA invA minusA multA divA eqA_dec n ltM ltM_dec (plusTerm (A:=A) plusA (n:=n) a c) b nZb (pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec p r) q)) in |- *.
rewrite <- pluspf_inv3b_eq with (1 := os) (a := a) (b := c) (p := p) (q := r); auto.
apply reduce_imp_reduceplus.
apply reducetop with (b := b) (nZb := nZb) (q := q); auto.
change (reduceplus Q (pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec (spminusf A A0 A1 eqA invA minusA multA divA eqA_dec n ltM ltM_dec a b nZb p q) (pX c r)) (spminusf A A0 A1 eqA invA minusA multA divA eqA_dec n ltM ltM_dec (plusTerm (A:=A) plusA (n:=n) a c) b nZb (pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec p r) q)) in |- *.
rewrite <- pluspf_inv2_eqa with (1 := os) (a := c) (p := spminusf A A0 A1 eqA invA minusA multA divA eqA_dec n ltM ltM_dec a b nZb p q) (q := r); auto.
apply reduce_imp_reduceplus.
apply reducetop with (b := b) (nZb := nZb) (q := q); auto.
apply (eqp_trans _ _ _ _ _ _ _ _ _ cs n) with (y := pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec (spminusf A A0 A1 eqA invA minusA multA divA eqA_dec n ltM ltM_dec a b nZb p q) (spminusf A A0 A1 eqA invA minusA multA divA eqA_dec n ltM ltM_dec c b nZb r q)); auto.
apply spminusf_plusTerm_r with (1 := cs); auto.
apply canonical_spminusf with (1 := cs); auto.
apply (eqp_sym _ _ _ _ _ _ _ _ _ cs n); auto.
apply spminusf_plusTerm with (1 := cs); auto.
Admitted.

Theorem one_plus_reduceplus : forall (Q : list (poly A0 eqA ltM)) (p1 p2 : list (Term A n)), reduce A A0 A1 eqA invA minusA multA divA eqA_dec n ltM ltM_dec Q p1 p2 -> forall r : list (Term A n), canonical A0 eqA ltM p1 -> canonical A0 eqA ltM r -> exists s : list (Term A n), reduceplus Q (pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec p1 r) s /\ reduceplus Q (pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec p2 r) s.
intros Q p1 p2 H'; elim H'; auto.
intros a b nZb p q r H'0 H'1 H'2 r0 H'3 H'4.
lapply (reduce_plus_top Q r0); [ intros H'7; elim (H'7 a b nZb p q); [ intros s E; elim E; intros H'16 H'17; clear E | idtac | idtac | idtac ] | idtac ]; auto.
exists s; split; auto.
cut (canonical A0 eqA ltM (pX b q)); [ intros C0 | apply inPolySet_imp_canonical with (L := Q); auto ].
apply reduceplus_eqp_com with (p := pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec (spminusf A A0 A1 eqA invA minusA multA divA eqA_dec n ltM ltM_dec a b nZb p q) r0) (q := s); auto.
apply canonical_pluspf with (1 := os); auto.
apply canonical_spminusf_full with (1 := cs); auto.
apply eqp_pluspf_com with (1 := cs); auto.
apply canonical_spminusf_full with (1 := cs); auto.
apply eqp_imp_canonical with (1 := cs) (p := spminusf A A0 A1 eqA invA minusA multA divA eqA_dec n ltM ltM_dec a b nZb p q); auto.
apply canonical_spminusf_full with (1 := cs); auto.
intros a b p q H'0 H'1 H'2 r H'3.
cut (canonical A0 eqA ltM p); [ intros C0 | apply canonical_imp_canonical with (a := a); auto ].
cut (~ zeroP (A:=A) A0 eqA (n:=n) a); [ intros Z0 | apply canonical_nzeroP with (ltM := ltM) (p := p); auto ].
cut (canonical A0 eqA ltM (pX a q)); [ intros C1 | idtac ].
cut (canonical A0 eqA ltM q); [ intros C2 | apply canonical_imp_canonical with (a := a); auto ].
elim r; auto.
intros H'4; exists (pX a q); split; auto.
apply reduceplus_eqp_com with (p := pX a p) (q := pX a q); auto.
apply (eqp_sym _ _ _ _ _ _ _ _ _ cs n); auto.
change (eqP A eqA n (pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec (pX a p) (pO A n)) (pX a p)) in |- *; auto.
apply reduceplus_eqp_com with (p := pX a q) (q := pX a q); auto.
apply (eqp_trans _ _ _ _ _ _ _ _ _ cs n) with (y := pX b q); auto.
apply (eqp_sym _ _ _ _ _ _ _ _ _ cs n); auto.
change (eqP A eqA n (pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec (pX b q) (pO A n)) (pX b q)) in |- *; auto.
clear r; intros c r H'4 H'5.
cut (canonical A0 eqA ltM r); [ intros C3 | apply canonical_imp_canonical with (a := c); auto ].
cut (~ zeroP (A:=A) A0 eqA (n:=n) c); [ intros Z1 | apply canonical_nzeroP with (ltM := ltM) (p := r); auto ].
case (ltT_dec A n ltM ltM_dec a c); [ intros temp; case temp; clear temp | idtac ]; intros test.
elim H'4; [ intros s E; elim E; intros H'7 H'8; try exact H'7; clear E H'4 | clear H'4 ]; auto.
exists (pX c s); split; auto.
change (reduceplus Q (pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec (pX a p) (pX c r)) (pX c s)) in |- *.
rewrite <- pluspf_inv2_eqa with (1 := os); auto.
cut (canonical A0 eqA ltM (pX b q)); [ intros C4 | apply canonical_pX_eqT with (a := a); auto ].
apply reduceplus_skip; auto.
rewrite pluspf_inv2_eqa with (1 := os); auto.
apply (eqTerm_imp_eqT A eqA); auto.
apply nzeroP_comp_eqTerm with (1 := cs) (a := a); auto.
change (reduceplus Q (pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec (pX b q) (pX c r)) (pX c s)) in |- *.
rewrite <- pluspf_inv2_eqa with (1 := os); auto.
apply reduceplus_skip; auto.
rewrite pluspf_inv2_eqa with (1 := os); auto.
apply canonical_pluspf with (1 := os); auto.
apply eqp_imp_canonical with (1 := cs) (p := pX a q); auto.
apply eqp_imp_canonical with (1 := cs) (p := pX c (pX a q)); auto.
apply eqp_imp_canonical with (1 := cs) (p := pX c (pX a q)); auto.
elim (H'1 (pX c r)); [ intros s E; elim E; intros H'9 H'10; clear E | idtac | idtac ]; auto.
cut (canonical A0 eqA ltM (pX b q)); [ intros C4 | apply canonical_pX_eqT with (a := a); auto ].
exists (pX a s); split; auto.
change (reduceplus Q (pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec (pX a p) (pX c r)) (pX a s)) in |- *.
rewrite <- pluspf_inv1_eq; auto.
apply reduceplus_skip; auto.
rewrite pluspf_inv1_eq; auto.
apply reduceplus_eqp_com with (p := pX a (pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec q (pX c r))) (q := pX a s); auto.
apply reduceplus_skip; auto.
rewrite pluspf_inv1_eq; auto.
rewrite pluspf_inv1_eq; auto.
rewrite pluspf_inv1_eq; auto.
apply (eqTerm_imp_eqT A eqA); auto.
apply nzeroP_comp_eqTerm with (1 := cs) (a := a); auto.
case (zeroP_dec A A0 eqA eqA_dec n (plusTerm (A:=A) plusA (n:=n) a c)); intros Z2.
elim (H'1 r); [ intros s E; elim E; intros H'9 H'10; clear E | idtac | idtac ]; auto.
exists s; split; auto.
change (reduceplus Q (pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec (pX a p) (pX c r)) s) in |- *.
rewrite <- pluspf_inv3a_eq; auto.
apply reduceplus_eqp_com with (p := pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec (pX a q) (pX c r)) (q := s); auto.
rewrite <- pluspf_inv3a_eq; auto.
apply eqp_pluspf_com with (1 := cs); auto.
apply eqp_imp_canonical with (1 := cs) (p := pX a q); auto.
elim (H'1 r); [ intros s E; elim E; intros H'9 H'10; clear E | idtac | idtac ]; auto.
exists (pX (plusTerm (A:=A) plusA (n:=n) a c) s); split; auto.
change (reduceplus Q (pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec (pX a p) (pX c r)) (pX (plusTerm (A:=A) plusA (n:=n) a c) s)) in |- *.
rewrite <- pluspf_inv3b_eq; auto.
apply reduceplus_skip; auto.
rewrite pluspf_inv3b_eq; auto.
apply reduceplus_eqp_com with (p := pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec (pX a q) (pX c r)) (q := pX (plusTerm (A:=A) plusA (n:=n) a c) s); auto.
rewrite <- pluspf_inv3b_eq; auto.
apply reduceplus_skip; auto.
rewrite pluspf_inv3b_eq; auto.
apply eqp_pluspf_com with (1 := cs); auto.
apply eqp_imp_canonical with (1 := cs) (p := pX a q); auto.
Admitted.

Theorem one_minus_reduceplus : forall (Q : list (poly A0 eqA ltM)) (p1 p2 : list (Term A n)), reduce A A0 A1 eqA invA minusA multA divA eqA_dec n ltM ltM_dec Q p1 p2 -> forall r : list (Term A n), canonical A0 eqA ltM p1 -> canonical A0 eqA ltM r -> exists s : list (Term A n), reduceplus Q (minuspf A A0 A1 eqA invA minusA multA eqA_dec n ltM ltM_dec p1 r) s /\ reduceplus Q (minuspf A A0 A1 eqA invA minusA multA eqA_dec n ltM ltM_dec p2 r) s.
intros Q p1 p2 H' r H'0 H'1.
lapply (one_plus_reduceplus Q p1 p2); [ intros H'5; elim (H'5 (mults (A:=A) multA (n:=n) (invTerm (A:=A) invA (n:=n) (T1 A1 n)) r)); [ intros s E; elim E; intros H'9 H'10; clear E | idtac | idtac ] | idtac ]; auto.
exists s; split; auto.
apply reduceplus_eqp_com with (p := pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec p1 (mults (A:=A) multA (n:=n) (invTerm (A:=A) invA (n:=n) (T1 A1 n)) r)) (q := s); auto.
apply (eqp_sym _ _ _ _ _ _ _ _ _ cs n); auto.
cut (canonical A0 eqA ltM p2); [ intros C0 | idtac ].
apply reduceplus_eqp_com with (p := pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec p2 (mults (A:=A) multA (n:=n) (invTerm (A:=A) invA (n:=n) (T1 A1 n)) r)) (q := s); auto.
apply (eqp_sym _ _ _ _ _ _ _ _ _ cs n); auto.
apply canonical_reduce with (1 := cs) (3 := H'); auto.
