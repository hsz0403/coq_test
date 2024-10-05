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
apply canonical_reduce with (eqA_dec := eqA_dec) (ltM_dec := ltM_dec) (Q := Q) (p := pX a p) (1 := cs); auto.
