Require Export Pspminus.
Section Preduce.
Load hCoefStructure.
Load hOrderStructure.
Load hSpminus.
Inductive inPolySet : list (Term A n) -> list (poly A0 eqA ltM) -> Prop := | incons : forall (a : Term A n) (p : list (Term A n)) (H : canonical A0 eqA ltM (pX a p)) (P : list (poly A0 eqA ltM)), inPolySet (pX a p) (exist (fun l0 : list (Term A n) => canonical A0 eqA ltM l0) (pX a p) H :: P) | inskip : forall (a : poly A0 eqA ltM) (p : list (Term A n)) (P : list (poly A0 eqA ltM)), inPolySet p P -> inPolySet p (a :: P).
Hint Resolve incons inskip : core.
Hint Resolve inPolySet_imp_canonical : core.
Inductive reduce (Q : list (poly A0 eqA ltM)) : list (Term A n) -> list (Term A n) -> Prop := | reducetop : forall (a b : Term A n) (nZb : ~ zeroP (A:=A) A0 eqA (n:=n) b) (p q r : list (Term A n)), inPolySet (pX b q) Q -> divP A A0 eqA multA divA n a b -> eqP A eqA n (spminusf A A0 A1 eqA invA minusA multA divA eqA_dec n ltM ltM_dec a b nZb p q) r -> reduce Q (pX a p) r | reduceskip : forall (a b : Term A n) (p q : list (Term A n)), reduce Q p q -> eqTerm (A:=A) eqA (n:=n) a b -> reduce Q (pX a p) (pX b q).
Hint Resolve reduceskip : core.
Hint Resolve reducetop_sp : core.
Hint Resolve reduce_mults : core.
Definition irreducible (Q : list (poly A0 eqA ltM)) (p : list (Term A n)) := forall q : list (Term A n), ~ reduce Q p q.
Hint Resolve pO_irreducible : core.
Inductive pickinSetp : Term A n -> list (Term A n) -> list (poly A0 eqA ltM) -> Prop := | pickinSeteqp : forall (a b : Term A n) (p : list (Term A n)) (H : canonical A0 eqA ltM (pX b p)) (P : list (poly A0 eqA ltM)), divP A A0 eqA multA divA n a b -> pickinSetp a (pX b p) (exist (fun l0 : list (Term A n) => canonical A0 eqA ltM l0) (pX b p) H :: P) | pickinSetskip : forall (a b : Term A n) (p : list (Term A n)) (q : poly A0 eqA ltM) (P : list (poly A0 eqA ltM)), pickinSetp a p P -> pickinSetp a p (q :: P).
Hint Resolve pickinSeteqp pickinSetskip : core.
Inductive reducehead (Q : list (poly A0 eqA ltM)) : list (Term A n) -> list (Term A n) -> Prop := reduceheadO : forall (a b : Term A n) (nZb : ~ zeroP (A:=A) A0 eqA (n:=n) b) (p q : list (Term A n)), pickinSetp a (pX b q) Q -> reducehead Q (pX a p) (spminusf A A0 A1 eqA invA minusA multA divA eqA_dec n ltM ltM_dec a b nZb p q).
Hint Resolve reduceheadO : core.
Definition s2p : poly A0 eqA ltM -> list (Term A n).
intros H'; elim H'.
intros x H'0; exact x.
Defined.
End Preduce.

Lemma inPolySet_imp_canonical : forall (p : list (Term A n)) (L : list (poly A0 eqA ltM)), inPolySet p L -> canonical A0 eqA ltM p.
Admitted.

Lemma not_nil_in_polySet_elm : forall (Q : list (poly A0 eqA ltM)) (p : list (Term A n)), inPolySet p Q -> p <> pO A n.
intros Q p H'; elim H'; auto.
Admitted.

Lemma inPolySet_is_pX : forall (p : list (Term A n)) (L : list (poly A0 eqA ltM)), inPolySet p L -> exists a : Term A n, (exists q : list (Term A n), p = pX a q).
intros p L H'; elim H'; auto.
Admitted.

Lemma pO_reduce : forall (Q : list (poly A0 eqA ltM)) (p : list (Term A n)), ~ reduce Q (pO A n) p.
Admitted.

Theorem reduce_in_pO : forall (Q : list (poly A0 eqA ltM)) (p : list (Term A n)), inPolySet p Q -> reduce Q p (pO A n).
intros Q p; case p; simpl in |- *; auto.
intros H'; elim (inPolySet_is_pX (pO A n) Q); [ intros a E; elim E; intros q E0; inversion E0 | idtac ]; auto.
intros a l H'.
cut (canonical A0 eqA ltM (pX a l)); [ intros Op0 | idtac ].
cut (canonical A0 eqA ltM l); [ intros Op1 | apply canonical_imp_canonical with (a := a) ]; auto.
cut (~ zeroP (A:=A) A0 eqA (n:=n) a); [ intros Nza | idtac ].
cut (spminusf A A0 A1 eqA invA minusA multA divA eqA_dec n ltM ltM_dec a a Nza l l = pO A n).
intros H'0; rewrite <- H'0.
change (reduce Q (pX a l) (spminusf A A0 A1 eqA invA minusA multA divA eqA_dec n ltM ltM_dec a a Nza l l)) in |- *.
apply reducetop with (b := a) (nZb := Nza) (q := l); auto.
apply divP_on_eqT with (1 := cs); auto.
cut (eqP A eqA n (spminusf A A0 A1 eqA invA minusA multA divA eqA_dec n ltM ltM_dec a a Nza l l) (pO A n)).
intros H'0; inversion H'0; auto.
apply (eqp_trans _ _ _ _ _ _ _ _ _ cs n) with (y := minuspf A A0 A1 eqA invA minusA multA eqA_dec n ltM ltM_dec l (mults (A:=A) multA (n:=n) (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n) a (b:=a) Nza) l)); auto.
apply (eqp_trans _ _ _ _ _ _ _ _ _ cs n) with (y := minuspf A A0 A1 eqA invA minusA multA eqA_dec n ltM ltM_dec l (mults (A:=A) multA (n:=n) (T1 A1 n) l)); auto.
apply (eqp_trans _ _ _ _ _ _ _ _ _ cs n) with (y := minuspf A A0 A1 eqA invA minusA multA eqA_dec n ltM ltM_dec l l); auto.
apply minuspf_refl with (1 := cs); auto.
apply (canonical_nzeroP A A0 eqA n ltM) with (p := l); auto.
Admitted.

Theorem ltP_reduce : forall (Q : list (poly A0 eqA ltM)) (p q : list (Term A n)), reduce Q p q -> canonical A0 eqA ltM p -> ltP (A:=A) (n:=n) ltM q p.
intros Q p q H'; elim H'; auto.
2: intros a b p0 q0 H'0 H'1 H'2 H'3; apply ltP_tl; auto.
2: apply (eqT_sym A n); apply (eqTerm_imp_eqT A eqA n); auto.
2: apply H'1; try apply canonical_imp_canonical with (a := a); auto.
intros a b nZb p0; case p0; auto.
intros q0 r H'0 H'1 H'2 H'3.
change (ltP (A:=A) (n:=n) ltM r (pX a (pO A n))) in |- *.
apply (canonical_pX_ltP A A0 eqA); auto.
apply eqp_imp_canonical with (1 := cs) (p := pX a (spminusf A A0 A1 eqA invA minusA multA divA eqA_dec n ltM ltM_dec a b nZb (pO A n) q0)); auto.
apply canonical_spminusf_full_t with (1 := cs); auto.
apply inPolySet_imp_canonical with (L := Q); auto.
intros t l q0 r H'0 H'1 H'2 H'3; apply ltP_trans with (y := pX a (pO A n)); auto.
apply (canonical_pX_ltP A A0 eqA); auto.
apply eqp_imp_canonical with (1 := cs) (p := pX a (spminusf A A0 A1 eqA invA minusA multA divA eqA_dec n ltM ltM_dec a b nZb (pX t l) q0)); auto.
apply canonical_spminusf_full_t with (1 := cs); auto.
apply inPolySet_imp_canonical with (L := Q); auto.
Admitted.

Theorem canonical_reduce : forall (Q : list (poly A0 eqA ltM)) (p q : list (Term A n)), reduce Q p q -> canonical A0 eqA ltM p -> canonical A0 eqA ltM q.
intros Q p q H'; elim H'; auto.
intros a b nZb p0 q0 r H'0 H'1 H'2 H'3.
apply eqp_imp_canonical with (1 := cs) (p := spminusf A A0 A1 eqA invA minusA multA divA eqA_dec n ltM ltM_dec a b nZb p0 q0); auto.
apply canonical_spminusf with (1 := cs); auto.
apply canonical_imp_canonical with (a := a); auto.
apply canonical_imp_canonical with (a := b); auto.
apply inPolySet_imp_canonical with (L := Q); auto.
intros a b p0 q0 H'0 H'1 H'2 H'3.
apply eqp_imp_canonical with (1 := cs) (p := pX a q0); auto.
cut (canonical A0 eqA ltM p0); [ intros C1 | apply canonical_imp_canonical with (a := a) ]; auto.
apply ltP_pX_canonical; auto.
apply canonical_nzeroP with (ltM := ltM) (p := p0); auto.
apply ltP_trans with (y := p0); auto.
apply ltP_reduce with (Q := Q); auto.
Admitted.

Theorem reduce_eqp_com : forall (Q : list (poly A0 eqA ltM)) (p q r s : list (Term A n)), reduce Q p q -> canonical A0 eqA ltM p -> eqP A eqA n p r -> eqP A eqA n q s -> reduce Q r s.
intros Q p q r s H'; generalize r s; clear r s; elim H'; auto.
intros a b nZb p0 q0 r H'0 H'1 H'2 r0 s H'3 H'4 H'5.
inversion_clear H'4.
apply reducetop with (b := b) (nZb := nZb) (q := q0); auto.
apply divP_eqTerm_comp with (1 := cs) (a := a); auto.
apply (eqp_trans _ _ _ _ _ _ _ _ _ cs n) with (y := spminusf A A0 A1 eqA invA minusA multA divA eqA_dec n ltM ltM_dec a b nZb p0 q0); auto.
cut (canonical A0 eqA ltM p0); [ intros Cp0 | apply canonical_imp_canonical with (a := a); auto ].
apply eqp_spminusf_com with (1 := cs); auto.
apply eqp_imp_canonical with (1 := cs) (p := p0); auto.
apply canonical_imp_canonical with (a := b); auto.
apply inPolySet_imp_canonical with (L := Q); auto.
apply (eqp_sym _ _ _ _ _ _ _ _ _ cs n); auto.
apply (eqTerm_sym _ _ _ _ _ _ _ _ _ cs n); auto.
apply divP_eqTerm_comp with (1 := cs) (a := a); auto.
apply (eqp_trans _ _ _ _ _ _ _ _ _ cs n) with (2 := H'5); auto.
intros a b p0 q0 H'0 H'1 H'2 r s H'3 H'4 H'5.
inversion_clear H'4.
inversion_clear H'5.
apply reduceskip; auto.
apply H'1; auto.
apply canonical_imp_canonical with (a := a); auto.
apply (eqTerm_trans _ _ _ _ _ _ _ _ _ cs n) with (y := a); auto.
apply (eqTerm_sym _ _ _ _ _ _ _ _ _ cs n); auto.
Admitted.

Theorem reduce_inv : forall (Q : list (poly A0 eqA ltM)) (a b : Term A n) (p q : list (Term A n)), reduce Q (pX a p) (pX b q) -> eqTerm (A:=A) eqA (n:=n) a b -> canonical A0 eqA ltM (pX a p) -> reduce Q p q.
intros Q a b p q H'; inversion_clear H'; auto.
intros eq Cap.
elim (not_double_canonical A A0 eqA n ltM) with (a := b) (p := q); auto.
apply eqp_imp_canonical with (p := pX b (spminusf A A0 A1 eqA invA minusA multA divA eqA_dec n ltM ltM_dec a b0 nZb p q0)) (1 := cs); auto.
apply (canonical_pX_eqT A A0 eqA n ltM) with (a := a); auto.
apply canonical_spminusf_full_t with (1 := cs); auto.
apply inPolySet_imp_canonical with (L := Q); auto.
apply (eqTerm_imp_eqT A eqA n); auto.
apply nzeroP_comp_eqTerm with (1 := cs) (a := a); auto.
Admitted.

Theorem reducetop_sp : forall (Q : list (poly A0 eqA ltM)) (a b : Term A n) (nZb : ~ zeroP (A:=A) A0 eqA (n:=n) b) (p q : list (Term A n)), inPolySet (pX b q) Q -> divP A A0 eqA multA divA n a b -> reduce Q (pX a p) (spminusf A A0 A1 eqA invA minusA multA divA eqA_dec n ltM ltM_dec a b nZb p q).
intros Q a b nZb p q H' H'0.
Admitted.

Theorem reduce_inv2 : forall (Q : list (poly A0 eqA ltM)) (p q : list (Term A n)), reduce Q p q -> canonical A0 eqA ltM p -> exists x : list (Term A n), (exists a : Term A n, ~ zeroP (A:=A) A0 eqA (n:=n) a /\ inPolySet x Q /\ canonical A0 eqA ltM x /\ eqP A eqA n q (minuspf A A0 A1 eqA invA minusA multA eqA_dec n ltM ltM_dec p (mults (A:=A) multA (n:=n) a x))).
intros Q p q H'; elim H'; auto.
intros a b nZb p0 q0 r H'0 H'1 H'2 H'3; cut (canonical A0 eqA ltM (pX b q0)); [ intros C1 | apply inPolySet_imp_canonical with (L := Q); auto ]; exists (pX b q0); exists (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n) a (b:=b) nZb); split; [ idtac | split; [ idtac | split; [ idtac | idtac ] ] ]; auto.
apply (eqp_trans _ _ _ _ _ _ _ _ _ cs n) with (y := spminusf A A0 A1 eqA invA minusA multA divA eqA_dec n ltM ltM_dec a b nZb p0 q0); auto.
apply (eqp_sym _ _ _ _ _ _ _ _ _ cs n); auto.
apply (eqp_trans _ _ _ _ _ _ _ _ _ cs n) with (y := spminusf A A0 A1 eqA invA minusA multA divA eqA_dec n ltM ltM_dec a b nZb (pX a p0) (pX b q0)); auto.
apply spminusf_extend with (1 := cs); auto.
intros a b p0 q0 H'0 H'1 H'2 H'3.
cut (canonical A0 eqA ltM p0); [ intros Op1 | apply canonical_imp_canonical with (a := a) ]; auto.
cut (canonical A0 eqA ltM (pX a q0)); [ intros Op2 | apply canonical_reduce with (Q := Q) (p := pX a p0) ]; auto.
cut (canonical A0 eqA ltM q0); [ intros Op3 | apply canonical_imp_canonical with (a := a) ]; auto.
elim H'1; [ intros x E; elim E; intros a0 E0; elim E0; intros H'4 H'5; elim H'5; intros H'6 H'7; elim H'7; intros H'8 H'9; clear H'7 H'5 E0 E H'1 | clear H'1 ]; auto.
exists x; exists a0; split; [ idtac | split; [ idtac | split ] ]; auto.
apply (eqp_trans _ _ _ _ _ _ _ _ _ cs n) with (y := pX a q0); [ auto | apply (eqp_sym _ _ _ _ _ _ _ _ _ cs n) ].
apply (eqp_sym _ _ _ _ _ _ _ _ _ cs n); auto.
apply (eqp_trans _ _ _ _ _ _ _ _ _ cs n) with (y := pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec (pX a p0) (mults (A:=A) multA (n:=n) (invTerm (A:=A) invA (n:=n) (T1 A1 n)) (mults (A:=A) multA (n:=n) a0 x))); [ auto | idtac ].
cut (~ zeroP (A:=A) A0 eqA (n:=n) a); [ intros Z0 | idtac ].
apply (eqp_trans _ _ _ _ _ _ _ _ _ cs n) with (y := pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec (pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec (pX a (pO A n)) p0) (mults (A:=A) multA (n:=n) (invTerm (A:=A) invA (n:=n) (T1 A1 n)) (mults (A:=A) multA (n:=n) a0 x))).
apply (eqp_sym _ _ _ _ _ _ _ _ _ cs n); apply eqp_pluspf_com with (1 := cs); auto.
apply plusTerm_is_pX with (1 := cs); auto.
apply (eqp_trans _ _ _ _ _ _ _ _ _ cs n) with (y := pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec (pX a (pO A n)) (pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec p0 (mults (A:=A) multA (n:=n) (invTerm (A:=A) invA (n:=n) (T1 A1 n)) (mults (A:=A) multA (n:=n) a0 x)))); [ auto | idtac ].
apply (eqp_trans _ _ _ _ _ _ _ _ _ cs n) with (y := pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec (pX a (pO A n)) (minuspf A A0 A1 eqA invA minusA multA eqA_dec n ltM ltM_dec p0 (mults (A:=A) multA (n:=n) a0 x))).
apply (eqp_sym _ _ _ _ _ _ _ _ _ cs n); auto.
apply (eqp_trans _ _ _ _ _ _ _ _ _ cs n) with (y := pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec (pX a (pO A n)) q0); auto.
apply (eqp_sym _ _ _ _ _ _ _ _ _ cs n); auto.
apply plusTerm_is_pX with (1 := cs); auto.
Admitted.

Theorem mults_eqp_inv : forall (a : Term A n) (p q : list (Term A n)), eqP A eqA n (mults (A:=A) multA (n:=n) a p) (mults (A:=A) multA (n:=n) a q) -> ~ zeroP (A:=A) A0 eqA (n:=n) a -> eqP A eqA n p q.
intros a p; elim p; auto.
intros q; case q; simpl in |- *; auto.
intros t l H'; inversion_clear H'; auto.
intros a0 l H' q; case q; simpl in |- *; auto.
intros H'0; inversion_clear H'0; auto.
intros t l0 H'0; inversion_clear H'0; auto.
intros H'1.
change (eqP A eqA n (pX a0 l) (pX t l0)) in |- *.
apply eqpP1; auto.
Admitted.

Theorem not_nil_in_polySet : forall (Q : list (poly A0 eqA ltM)) (p : list (Term A n)), ~ inPolySet (pO A n) Q.
intros Q H'; red in |- *; intros H'0.
lapply (not_nil_in_polySet_elm Q (pO A n)); [ intros H'3; apply H'3 || elim H'3 | idtac ]; auto.
