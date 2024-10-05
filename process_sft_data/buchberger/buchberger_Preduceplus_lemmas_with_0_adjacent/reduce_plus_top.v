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
apply canonical_spminusf_full_t with (1 := cs); auto.
