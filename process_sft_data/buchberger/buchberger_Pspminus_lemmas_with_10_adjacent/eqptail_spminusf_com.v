Require Export Pminus.
Require Export DivTerm.
Section Pspminus.
Load hCoefStructure.
Load hOrderStructure.
Load hMinus.
Hint Resolve divP_is_not_order : core.
Definition spminusf (a b : Term A n) (nZb : ~ zeroP (A:=A) A0 eqA (n:=n) b) (p q : list (Term A n)) := minuspf A A0 A1 eqA invA minusA multA eqA_dec n ltM ltM_dec p (mults (A:=A) multA (n:=n) (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n) a (b:=b) nZb) q).
Hint Resolve canonical_spminusf : core.
Hint Resolve canonical_spminusf_full : core.
Hint Resolve canonical_spminusf_full_t : core.
Hint Resolve spminusf_pluspf : core.
Hint Resolve eqTerm_spminusf_com eqp_spminusf_com eqp_spminusf_com : core.
Hint Resolve spminusf_plusTerm spminusf_multTerm : core.
Hint Resolve spminusf_minusTerm_r : core.
Hint Resolve spminusf_plusTerm_r : core.
Hint Resolve divP_minusTerm_comp : core.
Hint Resolve spminusf_minusTerm : core.
Hint Resolve spminusf_minusTerm : core.
End Pspminus.

Theorem divP_is_not_order : forall a b : Term A n, divP A A0 eqA multA divA n a b -> ~ ltT ltM a b.
intros a b H'; inversion H'.
case (ltT_dec A n ltM ltM_dec (T1 A1 n) (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n) a (b:=b) nZb)); [ intros tmp; case tmp; clear tmp | idtac ]; intros H'2; auto.
apply ltT_not_ltT; auto.
apply ltT_eqTl with (a := multTerm (A:=A) multA (n:=n) (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n) a (b:=b) nZb) b); auto.
apply (eqT_sym A n); apply (eqTerm_imp_eqT A eqA); auto.
apply ltT_eqTr with (a := multTerm (A:=A) multA (n:=n) (T1 A1 n) b); auto.
apply (eqT_sym A n); apply (eqTerm_imp_eqT A eqA); apply T1_multTerm_l with (1 := cs); auto.
apply multTerm_ltT_r with (1 := os); auto.
elim (T1_is_min_ltT A A1) with (a := divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n) a (b:=b) nZb) (1 := os); auto.
apply ltT_not_eqT; auto.
apply (eqT_trans A n) with (y := multTerm (A:=A) multA (n:=n) (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n) a (b:=b) nZb) b); auto.
apply (eqTerm_imp_eqT A eqA); auto.
apply (eqT_trans A n) with (y := multTerm (A:=A) multA (n:=n) (T1 A1 n) b); auto.
apply (eqT_sym A n); auto.
Admitted.

Theorem divP_ltT_comp : forall (a b : Term A n) (p : list (Term A n)), canonical A0 eqA ltM (pX b p) -> divP A A0 eqA multA divA n a b -> canonical A0 eqA ltM (pX a p).
intros a b p; case p; auto.
intros H' H'0.
change (canonical A0 eqA ltM (pX a (pO A n))) in |- *; apply canonicalp1; auto.
apply divP_inv1 with (1 := H'0); auto.
intros a0 l H' H'0; change (canonical A0 eqA ltM (pX a (pX a0 l))) in |- *; apply canonical_cons; auto.
case (ltT_dec A n ltM ltM_dec a b); [ intros tmp; case tmp; clear tmp | idtac ]; intros H'2; auto.
elim (divP_is_not_order a b); auto.
apply (ltT_trans A _ _ os) with (y := b); auto.
apply (canonical_pX_order _ A0 eqA) with (l := l); auto.
apply eqT_compat_ltTr with (b := b); auto.
apply (eqT_sym A n); auto.
apply (canonical_pX_order _ A0 eqA) with (l := l); auto.
apply divP_inv1 with (1 := H'0); auto.
Admitted.

Theorem sp_rew : forall (a b : Term A n) (nZ1 nZ2 : ~ zeroP (A:=A) A0 eqA (n:=n) b) (p q : list (Term A n)), spminusf a b nZ1 p q = spminusf a b nZ2 p q.
auto; auto.
intros a b nZ1 nZ2 p q; unfold spminusf in |- *.
change (minuspf A A0 A1 eqA invA minusA multA eqA_dec n ltM ltM_dec p (mults (A:=A) multA (n:=n) (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n) a (b:=b) nZ1) q) = minuspf A A0 A1 eqA invA minusA multA eqA_dec n ltM ltM_dec p (mults (A:=A) multA (n:=n) (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n) a (b:=b) nZ2) q)) in |- *.
Admitted.

Theorem rew_spminusf : forall (a b : Term A n) (nZb : ~ zeroP (A:=A) A0 eqA (n:=n) b) (p q : list (Term A n)), spminusf a b nZb p q = minuspf A A0 A1 eqA invA minusA multA eqA_dec n ltM ltM_dec p (mults (A:=A) multA (n:=n) (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n) a (b:=b) nZb) q).
Admitted.

Theorem canonical_spminusf : forall (a b : Term A n) (nZb : ~ zeroP (A:=A) A0 eqA (n:=n) b) (p q : list (Term A n)), canonical A0 eqA ltM p -> canonical A0 eqA ltM q -> divP A A0 eqA multA divA n a b -> canonical A0 eqA ltM (spminusf a b nZb p q).
unfold spminusf in |- *.
Admitted.

Theorem spminusf_extend : forall (a b : Term A n) (nZb : ~ zeroP (A:=A) A0 eqA (n:=n) b) (p q : list (Term A n)), divP A A0 eqA multA divA n a b -> canonical A0 eqA ltM (pX a p) -> canonical A0 eqA ltM (pX b q) -> eqP A eqA n (spminusf a b nZb p q) (spminusf a b nZb (pX a p) (pX b q)).
intros a b nZb p q H'; unfold spminusf in |- *; simpl in |- *; inversion H'.
intros H'0 H'1; apply (eqp_trans _ _ _ _ _ _ _ _ _ cs n) with (y := minuspf A A0 A1 eqA invA minusA multA eqA_dec n ltM ltM_dec (pX a p) (pX a (mults (A:=A) multA (n:=n) (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n) a (b:=b) nZb) q))); auto.
apply minuspf_inv3a with (1 := cs); auto.
apply minuspf_comp with (1 := cs); auto.
apply canonical_pX_eqT with (a := multTerm (A:=A) multA (n:=n) (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n) a (b:=b) nZb) b); auto.
change (canonical A0 eqA ltM (mults (A:=A) multA (n:=n) (divTerm divA a nZb) (pX b q))) in |- *; auto.
apply (eqT_sym A n); apply (eqTerm_imp_eqT A eqA n); auto.
Admitted.

Theorem canonical_spminusf_full : forall (a b : Term A n) (nZb : ~ zeroP (A:=A) A0 eqA (n:=n) b) (p q : list (Term A n)), canonical A0 eqA ltM (pX a p) -> canonical A0 eqA ltM (pX b q) -> divP A A0 eqA multA divA n a b -> canonical A0 eqA ltM (spminusf a b nZb p q).
intros a b nZb p q H' H'0 H'1; apply canonical_spminusf; auto.
apply canonical_imp_canonical with (a := a); auto.
Admitted.

Theorem canonical_spminusf_full_t : forall (a b : Term A n) (nZb : ~ zeroP (A:=A) A0 eqA (n:=n) b) (p q : list (Term A n)), canonical A0 eqA ltM (pX a p) -> canonical A0 eqA ltM (pX b q) -> divP A A0 eqA multA divA n a b -> canonical A0 eqA ltM (pX a (spminusf a b nZb p q)).
unfold spminusf in |- *.
intros a b nZb p q H' H'0 H'1; try assumption.
inversion H'1.
apply order_minuspf with (1 := cs); auto.
apply canonical_pX_eqT with (a := multTerm (A:=A) multA (n:=n) (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n) a (b:=b) nZb) b); auto.
change (canonical A0 eqA ltM (mults (A:=A) multA (n:=n) (divTerm divA a nZb) (pX b q))) in |- *; auto.
Admitted.

Theorem spminusf_pluspf : forall (a b : Term A n) (nZb : ~ zeroP (A:=A) A0 eqA (n:=n) b) (p q r : list (Term A n)), canonical A0 eqA ltM p -> canonical A0 eqA ltM q -> canonical A0 eqA ltM r -> divP A A0 eqA multA divA n a b -> eqP A eqA n (spminusf a b nZb (pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec p q) r) (pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec (spminusf a b nZb p r) q).
intros a b nZb p q r H' H'0 H'1 H'2; unfold spminusf in |- *.
inversion H'2.
apply (eqp_trans _ _ _ _ _ _ _ _ _ cs n) with (y := pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec (pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec p q) (mults (A:=A) multA (n:=n) (invTerm (A:=A) invA (n:=n) (T1 A1 n)) (mults (A:=A) multA (n:=n) (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n) a (b:=b) nZb) r))); auto.
apply (eqp_trans _ _ _ _ _ _ _ _ _ cs n) with (y := pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec p (pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec q (mults (A:=A) multA (n:=n) (invTerm (A:=A) invA (n:=n) (T1 A1 n)) (mults (A:=A) multA (n:=n) (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n) a (b:=b) nZb) r)))); auto.
apply (eqp_trans _ _ _ _ _ _ _ _ _ cs n) with (y := pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec p (pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec (mults (A:=A) multA (n:=n) (invTerm (A:=A) invA (n:=n) (T1 A1 n)) (mults (A:=A) multA (n:=n) (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n) a (b:=b) nZb) r)) q)); auto.
apply eqp_pluspf_com with (1 := cs); auto.
apply (eqp_trans _ _ _ _ _ _ _ _ _ cs n) with (y := pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec (pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec p (mults (A:=A) multA (n:=n) (invTerm (A:=A) invA (n:=n) (T1 A1 n)) (mults (A:=A) multA (n:=n) (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n) a (b:=b) nZb) r))) q); apply (eqp_sym _ _ _ _ _ _ _ _ _ cs n); auto.
Admitted.

Theorem eqTerm_spminusf_com : forall (a b c : Term A n) (nZc : ~ zeroP (A:=A) A0 eqA (n:=n) c) (p q : list (Term A n)), canonical A0 eqA ltM p -> canonical A0 eqA ltM q -> eqTerm (A:=A) eqA (n:=n) a b -> divP A A0 eqA multA divA n a c -> eqP A eqA n (spminusf a c nZc p q) (spminusf b c nZc p q).
intros a b c nZc p q H' H'0 H'1 H'2.
cut (divP A A0 eqA multA divA n b c); [ intros H'3 | auto ].
unfold spminusf in |- *; auto.
Admitted.

Theorem eqp_spminusf_com : forall (a b c : Term A n) (nZc : ~ zeroP (A:=A) A0 eqA (n:=n) c) (p q r : list (Term A n)), canonical A0 eqA ltM p -> canonical A0 eqA ltM q -> canonical A0 eqA ltM r -> eqP A eqA n p q -> eqTerm (A:=A) eqA (n:=n) a b -> divP A A0 eqA multA divA n a c -> eqP A eqA n (spminusf a c nZc p r) (spminusf b c nZc q r).
intros a b c nZc p q r H' H'0 H'1 H'2 H'3 H'4.
apply (eqp_trans _ _ _ _ _ _ _ _ _ cs n) with (y := spminusf b c nZc p r); auto.
apply eqTerm_spminusf_com; auto.
apply eqptail_spminusf_com; auto.
Admitted.

Theorem spminusf_minuspf : forall (a b : Term A n) (nZb : ~ zeroP (A:=A) A0 eqA (n:=n) b) (p q r : list (Term A n)), canonical A0 eqA ltM p -> canonical A0 eqA ltM q -> canonical A0 eqA ltM r -> divP A A0 eqA multA divA n a b -> eqP A eqA n (spminusf a b nZb (minuspf A A0 A1 eqA invA minusA multA eqA_dec n ltM ltM_dec p q) r) (minuspf A A0 A1 eqA invA minusA multA eqA_dec n ltM ltM_dec (spminusf a b nZb p r) q).
intros a b nZb p q r H' H'0 H'1 H'2; try assumption.
apply (eqp_trans _ _ _ _ _ _ _ _ _ cs n) with (y := spminusf a b nZb (pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec p (mults (A:=A) multA (n:=n) (invTerm (A:=A) invA (n:=n) (T1 A1 n)) q)) r); auto.
apply (eqp_trans _ _ _ _ _ _ _ _ _ cs n) with (y := pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec (spminusf a b nZb p r) (mults (A:=A) multA (n:=n) (invTerm (A:=A) invA (n:=n) (T1 A1 n)) q)); auto.
Admitted.

Theorem spminusf_plusTerm : forall (a b c : Term A n) (nZc : ~ zeroP (A:=A) A0 eqA (n:=n) c) (p q r : list (Term A n)), canonical A0 eqA ltM p -> canonical A0 eqA ltM q -> canonical A0 eqA ltM r -> divP A A0 eqA multA divA n a c -> divP A A0 eqA multA divA n b c -> eqT a b -> ~ zeroP (A:=A) A0 eqA (n:=n) (plusTerm (A:=A) plusA (n:=n) a b) -> eqP A eqA n (spminusf (plusTerm (A:=A) plusA (n:=n) a b) c nZc (pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec p q) r) (pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec (spminusf a c nZc p r) (spminusf b c nZc q r)).
intros a b c nZc p q r H' H'0 H'1 H'2 H'3 H'4 H'5; unfold spminusf in |- *.
apply (eqp_sym _ _ _ _ _ _ _ _ _ cs n); apply (eqp_trans _ _ _ _ _ _ _ _ _ cs n) with (y := pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec (pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec p (mults (A:=A) multA (n:=n) (invTerm (A:=A) invA (n:=n) (T1 A1 n)) (mults (A:=A) multA (n:=n) (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n) a (b:=c) nZc) r))) (pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec q (mults (A:=A) multA (n:=n) (invTerm (A:=A) invA (n:=n) (T1 A1 n)) (mults (A:=A) multA (n:=n) (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n) b (b:=c) nZc) r)))); [ auto | idtac ].
apply eqp_pluspf_com with (1 := cs); auto.
apply (eqp_trans _ _ _ _ _ _ _ _ _ cs n) with (y := pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec p (pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec (mults (A:=A) multA (n:=n) (invTerm (A:=A) invA (n:=n) (T1 A1 n)) (mults (A:=A) multA (n:=n) (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n) a (b:=c) nZc) r)) (pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec q (mults (A:=A) multA (n:=n) (invTerm (A:=A) invA (n:=n) (T1 A1 n)) (mults (A:=A) multA (n:=n) (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n) b (b:=c) nZc) r))))); [ auto | idtac ].
apply pluspf_assoc with (1 := cs); auto.
apply (eqp_trans _ _ _ _ _ _ _ _ _ cs n) with (y := pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec p (pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec (pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec (mults (A:=A) multA (n:=n) (invTerm (A:=A) invA (n:=n) (T1 A1 n)) (mults (A:=A) multA (n:=n) (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n) a (b:=c) nZc) r)) q) (mults (A:=A) multA (n:=n) (invTerm (A:=A) invA (n:=n) (T1 A1 n)) (mults (A:=A) multA (n:=n) (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n) b (b:=c) nZc) r)))).
apply (eqp_sym _ _ _ _ _ _ _ _ _ cs n); auto 8.
apply (eqp_trans _ _ _ _ _ _ _ _ _ cs n) with (y := pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec p (pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec (pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec q (mults (A:=A) multA (n:=n) (invTerm (A:=A) invA (n:=n) (T1 A1 n)) (mults (A:=A) multA (n:=n) (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n) a (b:=c) nZc) r))) (mults (A:=A) multA (n:=n) (invTerm (A:=A) invA (n:=n) (T1 A1 n)) (mults (A:=A) multA (n:=n) (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n) b (b:=c) nZc) r)))); [ auto 8 | idtac ].
apply (eqp_trans _ _ _ _ _ _ _ _ _ cs n) with (y := pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec p (pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec q (pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec (mults (A:=A) multA (n:=n) (invTerm (A:=A) invA (n:=n) (T1 A1 n)) (mults (A:=A) multA (n:=n) (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n) a (b:=c) nZc) r)) (mults (A:=A) multA (n:=n) (invTerm (A:=A) invA (n:=n) (T1 A1 n)) (mults (A:=A) multA (n:=n) (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n) b (b:=c) nZc) r))))); [ auto 10 | idtac ].
apply (eqp_trans _ _ _ _ _ _ _ _ _ cs n) with (y := pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec (pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec p q) (pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec (mults (A:=A) multA (n:=n) (invTerm (A:=A) invA (n:=n) (T1 A1 n)) (mults (A:=A) multA (n:=n) (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n) a (b:=c) nZc) r)) (mults (A:=A) multA (n:=n) (invTerm (A:=A) invA (n:=n) (T1 A1 n)) (mults (A:=A) multA (n:=n) (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n) b (b:=c) nZc) r)))).
apply (eqp_sym _ _ _ _ _ _ _ _ _ cs n); auto.
apply pluspf_assoc with (1 := cs); auto.
apply (eqp_sym _ _ _ _ _ _ _ _ _ cs n); apply (eqp_trans _ _ _ _ _ _ _ _ _ cs n) with (y := pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec (pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec p q) (mults (A:=A) multA (n:=n) (invTerm (A:=A) invA (n:=n) (T1 A1 n)) (mults (A:=A) multA (n:=n) (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n) (plusTerm (A:=A) plusA (n:=n) a b) (b:=c) nZc) r))); [ auto | idtac ].
apply eqp_pluspf_com with (1 := cs); auto.
apply (eqp_trans _ _ _ _ _ _ _ _ _ cs n) with (y := mults (A:=A) multA (n:=n) (invTerm (A:=A) invA (n:=n) (T1 A1 n)) (pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec (mults (A:=A) multA (n:=n) (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n) a (b:=c) nZc) r) (mults (A:=A) multA (n:=n) (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n) b (b:=c) nZc) r))).
apply mults_comp with (1 := cs); auto.
apply (eqp_trans _ _ _ _ _ _ _ _ _ cs n) with (y := mults (A:=A) multA (n:=n) (plusTerm (A:=A) plusA (n:=n) (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n) a (b:=c) nZc) (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n) b (b:=c) nZc)) r).
apply mults_comp with (1 := cs); auto.
apply eqT_divTerm_plusTerm with (1 := cs); auto.
inversion H'2; auto.
inversion H'3; auto.
apply mults_dist1 with (1 := cs); auto.
inversion H'2; inversion H'3; auto.
apply nzeroP_comp_eqTerm with (1 := cs) (a := divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n) (plusTerm (A:=A) plusA (n:=n) a b) (b:=c) nZc); auto.
apply eqT_divTerm_plusTerm with (1 := cs); auto.
Admitted.

Theorem spminusf_multTerm : forall (a b c : Term A n) (nZc : ~ zeroP (A:=A) A0 eqA (n:=n) c) (p q : list (Term A n)), canonical A0 eqA ltM p -> canonical A0 eqA ltM q -> divP A A0 eqA multA divA n b c -> ~ zeroP (A:=A) A0 eqA (n:=n) a -> eqP A eqA n (spminusf (multTerm (A:=A) multA (n:=n) a b) c nZc (mults (A:=A) multA (n:=n) a p) q) (mults (A:=A) multA (n:=n) a (spminusf b c nZc p q)).
intros a b c nZc p q H' H'0 H'1 H'2; unfold spminusf in |- *.
apply (eqp_trans _ _ _ _ _ _ _ _ _ cs n) with (y := minuspf A A0 A1 eqA invA minusA multA eqA_dec n ltM ltM_dec (mults (A:=A) multA (n:=n) a p) (mults (A:=A) multA (n:=n) (multTerm (A:=A) multA (n:=n) a (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n) b (b:=c) nZc)) q)); [ auto | idtac ].
apply minuspf_comp with (1 := cs); auto.
apply canonical_mults with (1 := cs); auto.
apply nzeroP_comp_eqTerm with (1 := cs) (a := multTerm (A:=A) multA (n:=n) a (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n) b (b:=c) nZc)); auto.
apply (eqTerm_sym _ _ _ _ _ _ _ _ _ cs n); apply divTerm_multTerm_l with (1 := cs).
inversion H'1; auto.
apply (eqp_trans _ _ _ _ _ _ _ _ _ cs n) with (y := minuspf A A0 A1 eqA invA minusA multA eqA_dec n ltM ltM_dec (mults (A:=A) multA (n:=n) a p) (mults (A:=A) multA (n:=n) a (mults (A:=A) multA (n:=n) (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n) b (b:=c) nZc) q))); [ auto | idtac ].
Admitted.

Theorem spminusf_minusTerm_l : forall (a b : Term A n) (nZb : ~ zeroP (A:=A) A0 eqA (n:=n) b) (p q r : list (Term A n)), canonical A0 eqA ltM p -> canonical A0 eqA ltM q -> canonical A0 eqA ltM r -> divP A A0 eqA multA divA n a b -> eqP A eqA n (spminusf a b nZb (minuspf A A0 A1 eqA invA minusA multA eqA_dec n ltM ltM_dec p q) r) (minuspf A A0 A1 eqA invA minusA multA eqA_dec n ltM ltM_dec (spminusf a b nZb p r) q).
intros a b nZb p q r H' H'0 H'1 H'2.
apply (eqp_trans _ _ _ _ _ _ _ _ _ cs n) with (y := spminusf a b nZb (pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec p (mults (A:=A) multA (n:=n) (invTerm (A:=A) invA (n:=n) (T1 A1 n)) q)) r); [ auto | idtac ].
apply (eqp_trans _ _ _ _ _ _ _ _ _ cs n) with (y := pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec (spminusf a b nZb p r) (mults (A:=A) multA (n:=n) (invTerm (A:=A) invA (n:=n) (T1 A1 n)) q)); [ auto | idtac ].
Admitted.

Theorem spminusf_plusTerm_l : forall (a b : Term A n) (nZb : ~ zeroP (A:=A) A0 eqA (n:=n) b) (p q r : list (Term A n)), canonical A0 eqA ltM p -> canonical A0 eqA ltM q -> canonical A0 eqA ltM r -> divP A A0 eqA multA divA n a b -> eqP A eqA n (spminusf a b nZb (pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec p q) r) (pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec (spminusf a b nZb p r) q).
intros a b nZb p q r H' H'0 H'1 H'2.
apply (eqp_trans _ _ _ _ _ _ _ _ _ cs n) with (y := pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec (spminusf a b nZb p r) q); [ auto | idtac ].
Admitted.

Theorem spminusf_minusTerm_r : forall (a b : Term A n) (nZb : ~ zeroP (A:=A) A0 eqA (n:=n) b) (p q r : list (Term A n)), canonical A0 eqA ltM p -> canonical A0 eqA ltM q -> canonical A0 eqA ltM r -> divP A A0 eqA multA divA n a b -> eqP A eqA n (spminusf a b nZb (minuspf A A0 A1 eqA invA minusA multA eqA_dec n ltM ltM_dec p q) r) (minuspf A A0 A1 eqA invA minusA multA eqA_dec n ltM ltM_dec p (spminusf (invTerm (A:=A) invA (n:=n) a) b nZb q r)).
intros a b nZb p q r H' H'0 H'1 H'2; try assumption.
apply (eqp_trans _ _ _ _ _ _ _ _ _ cs n) with (y := spminusf a b nZb (pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec p (mults (A:=A) multA (n:=n) (invTerm (A:=A) invA (n:=n) (T1 A1 n)) q)) r); [ auto | idtac ].
apply (eqp_trans _ _ _ _ _ _ _ _ _ cs n) with (y := spminusf a b nZb (pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec (mults (A:=A) multA (n:=n) (invTerm (A:=A) invA (n:=n) (T1 A1 n)) q) p) r); [ auto | idtac ].
apply (eqp_trans _ _ _ _ _ _ _ _ _ cs n) with (y := pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec (spminusf a b nZb (mults (A:=A) multA (n:=n) (invTerm (A:=A) invA (n:=n) (T1 A1 n)) q) r) p); [ auto | idtac ].
apply (eqp_trans _ _ _ _ _ _ _ _ _ cs n) with (y := pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec p (spminusf a b nZb (mults (A:=A) multA (n:=n) (invTerm (A:=A) invA (n:=n) (T1 A1 n)) q) r)); [ auto | idtac ].
apply (eqp_sym _ _ _ _ _ _ _ _ _ cs n); apply (eqp_trans _ _ _ _ _ _ _ _ _ cs n) with (y := pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec p (mults (A:=A) multA (n:=n) (invTerm (A:=A) invA (n:=n) (T1 A1 n)) (spminusf (invTerm (A:=A) invA (n:=n) a) b nZb q r))); [ auto | idtac ].
apply eqp_pluspf_com with (1 := cs); auto.
apply (eqp_trans _ _ _ _ _ _ _ _ _ cs n) with (y := spminusf (multTerm (A:=A) multA (n:=n) (invTerm (A:=A) invA (n:=n) (T1 A1 n)) (invTerm (A:=A) invA (n:=n) a)) b nZb (mults (A:=A) multA (n:=n) (invTerm (A:=A) invA (n:=n) (T1 A1 n)) q) r); [ apply (eqp_sym _ _ _ _ _ _ _ _ _ cs n); auto | idtac ].
apply (eqp_trans _ _ _ _ _ _ _ _ _ cs n) with (y := spminusf (invTerm (A:=A) invA (n:=n) (multTerm (A:=A) multA (n:=n) (T1 A1 n) (invTerm (A:=A) invA (n:=n) a))) b nZb (mults (A:=A) multA (n:=n) (invTerm (A:=A) invA (n:=n) (T1 A1 n)) q) r); [ auto | idtac ].
apply eqTerm_spminusf_com; auto.
apply (divP_trans _ _ _ _ _ _ _ _ _ cs n) with (y := invTerm (A:=A) invA (n:=n) a); auto.
apply divTerm_multTermr with (1 := cs); auto.
apply nZero_invTerm_nZero with (1 := cs); auto.
apply divP_inv1 with (1 := H'2); auto.
apply (eqp_trans _ _ _ _ _ _ _ _ _ cs n) with (y := spminusf (invTerm (A:=A) invA (n:=n) (invTerm (A:=A) invA (n:=n) a)) b nZb (mults (A:=A) multA (n:=n) (invTerm (A:=A) invA (n:=n) (T1 A1 n)) q) r); auto.
apply eqp_spminusf_com; auto.
apply (eqTerm_sym _ _ _ _ _ _ _ _ _ cs n); auto.
apply divP_invTerm_l with (1 := cs); auto.
apply divP_eqTerm_comp with (a := invTerm (A:=A) invA (n:=n) a) (1 := cs); auto.
apply eqTerm_spminusf_com; auto.
Admitted.

Theorem spminusf_plusTerm_r : forall (a b : Term A n) (nZb : ~ zeroP (A:=A) A0 eqA (n:=n) b) (p q r : list (Term A n)), canonical A0 eqA ltM p -> canonical A0 eqA ltM q -> canonical A0 eqA ltM r -> divP A A0 eqA multA divA n a b -> eqP A eqA n (spminusf a b nZb (pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec p q) r) (pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec p (spminusf a b nZb q r)).
intros a b nZb p q r H' H'0 H'1 H'2; try assumption.
apply (eqp_trans _ _ _ _ _ _ _ _ _ cs n) with (y := spminusf a b nZb (pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec q p) r); [ auto | idtac ].
apply (eqp_trans _ _ _ _ _ _ _ _ _ cs n) with (y := pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec (spminusf a b nZb q r) p); [ auto | idtac ].
Admitted.

Theorem divP_minusTerm_comp : forall a b c : Term A n, divP A A0 eqA multA divA n a c -> divP A A0 eqA multA divA n b c -> eqT a b -> ~ zeroP (A:=A) A0 eqA (n:=n) (minusTerm (A:=A) minusA (n:=n) a b) -> divP A A0 eqA multA divA n (minusTerm (A:=A) minusA (n:=n) a b) c.
intros a b c H' H'0 H'1 H'2.
apply divP_eqTerm_comp with (a := plusTerm (A:=A) plusA (n:=n) a (invTerm (A:=A) invA (n:=n) b)) (1 := cs); auto.
apply divP_plusTerm with (1 := cs); auto.
apply (eqT_trans A n) with (1 := H'1); auto.
apply nzeroP_comp_eqTerm with (1 := cs) (a := minusTerm (A:=A) minusA (n:=n) a b); auto.
Admitted.

Theorem eqptail_spminusf_com : forall (a b : Term A n) (nZb : ~ zeroP (A:=A) A0 eqA (n:=n) b) (p q r : list (Term A n)), canonical A0 eqA ltM p -> canonical A0 eqA ltM q -> canonical A0 eqA ltM r -> eqP A eqA n p q -> divP A A0 eqA multA divA n a b -> eqP A eqA n (spminusf a b nZb p r) (spminusf a b nZb q r).
unfold spminusf in |- *; auto.
