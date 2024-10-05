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

Theorem reduce_mults_inv_lem : forall (Q : list (poly A0 eqA ltM)) (p q : list (Term A n)), reduce Q p q -> forall r : list (Term A n), canonical A0 eqA ltM r -> p = mults (A:=A) multA (n:=n) (invTerm (A:=A) invA (n:=n) (T1 A1 n)) r -> reduce Q r (mults (A:=A) multA (n:=n) (invTerm (A:=A) invA (n:=n) (T1 A1 n)) q).
intros Q p q H'; elim H'; clear H'; auto.
2: intros a b p0 q0 H' H'0 H'1 r; case r; auto.
2: intros H'2 H'3; inversion_clear H'3; auto.
2: intros a0 l H'2 H'3.
2: change (reduce Q (pX a0 l) (pX (multTerm (A:=A) multA (n:=n) (invTerm (A:=A) invA (n:=n) (T1 A1 n)) b) (mults (A:=A) multA (n:=n) (invTerm (A:=A) invA (n:=n) (T1 A1 n)) q0))) in |- *.
2: apply reduceskip; auto.
2: apply H'0; auto.
2: apply canonical_imp_canonical with (a := a0); auto.
2: inversion_clear H'3; auto.
2: apply (eqTerm_trans _ _ _ _ _ _ _ _ _ cs n) with (y := multTerm (A:=A) multA (n:=n) (invTerm (A:=A) invA (n:=n) (T1 A1 n)) a); auto.
2: replace a with (multTerm (A:=A) multA (n:=n) (invTerm (A:=A) invA (n:=n) (T1 A1 n)) a0); [ idtac | inversion H'3 ]; auto.
2: apply (eqTerm_trans _ _ _ _ _ _ _ _ _ cs n) with (y := multTerm (A:=A) multA (n:=n) (T1 A1 n) a0); auto.
2: apply (eqTerm_trans _ _ _ _ _ _ _ _ _ cs n) with (y := multTerm (A:=A) multA (n:=n) (multTerm (A:=A) multA (n:=n) (invTerm (A:=A) invA (n:=n) (T1 A1 n)) (invTerm (A:=A) invA (n:=n) (T1 A1 n))) a0); apply (eqTerm_sym _ _ _ _ _ _ _ _ _ cs n); auto.
intros a b nZb p0 q0 r H' H'0 H'1 r0; case r0; auto.
intros; discriminate.
intros a0 l H'2 H'3.
change (pX a p0 = pX (multTerm (A:=A) multA (n:=n) (invTerm (A:=A) invA (n:=n) (T1 A1 n)) a0) (mults (A:=A) multA (n:=n) (invTerm (A:=A) invA (n:=n) (T1 A1 n)) l)) in H'3.
cut (canonical A0 eqA ltM l); try apply canonical_imp_canonical with (a := a0); auto; intros C0.
change (reduce Q (pX a0 l) (mults multA (invTerm invA (T1 A1 n)) r)) in |- *.
apply reducetop with (b := b) (nZb := nZb) (q := q0); auto.
apply divP_eqT with (1 := cs) (a := a); auto.
rewrite pX_invl with (1 := H'3); auto.
apply (eqT_sym A n); apply (eqT_trans A n) with (y := multTerm (A:=A) multA (n:=n) (T1 A1 n) a0); auto.
apply (eqTerm_imp_eqT A eqA n); auto.
apply canonical_nzeroP with (ltM := ltM) (p := l); auto.
cut (canonical A0 eqA ltM (pX b q0)); try apply inPolySet_imp_canonical with (L := Q); auto; intros C1.
cut (canonical A0 eqA ltM q0); try apply canonical_imp_canonical with (a := b); auto; intros C2.
cut (canonical A0 eqA ltM (pX a p0)); [ intros C3 | idtac ]; auto.
cut (canonical A0 eqA ltM p0); try apply canonical_imp_canonical with (a := a); auto; intros C4.
cut (divP A A0 eqA multA divA n a0 b); [ intros divP0 | idtac ].
apply (eqp_trans _ _ _ _ _ _ _ _ _ cs n) with (y := mults (A:=A) multA (n:=n) (invTerm (A:=A) invA (n:=n) (T1 A1 n)) (spminusf A A0 A1 eqA invA minusA multA divA eqA_dec n ltM ltM_dec a b nZb p0 q0)).
apply (eqp_sym _ _ _ _ _ _ _ _ _ cs n); apply (eqp_trans _ _ _ _ _ _ _ _ _ cs n) with (y := spminusf A A0 A1 eqA invA minusA multA divA eqA_dec n ltM ltM_dec (multTerm (A:=A) multA (n:=n) (invTerm (A:=A) invA (n:=n) (T1 A1 n)) a) b nZb (mults (A:=A) multA (n:=n) (invTerm (A:=A) invA (n:=n) (T1 A1 n)) p0) q0); auto.
apply (eqp_sym _ _ _ _ _ _ _ _ _ cs n).
apply spminusf_multTerm with (1 := cs); auto.
apply (eqp_trans _ _ _ _ _ _ _ _ _ cs n) with (y := spminusf A A0 A1 eqA invA minusA multA divA eqA_dec n ltM ltM_dec a0 b nZb (mults (A:=A) multA (n:=n) (invTerm (A:=A) invA (n:=n) (T1 A1 n)) p0) q0); auto.
apply eqTerm_spminusf_com with (1 := cs); auto.
rewrite pX_invl with (1 := H'3); auto.
apply (eqTerm_trans _ _ _ _ _ _ _ _ _ cs n) with (multTerm (A:=A) multA (n:=n) (multTerm (A:=A) multA (n:=n) (invTerm (A:=A) invA (n:=n) (T1 A1 n)) (invTerm (A:=A) invA (n:=n) (T1 A1 n))) a0); auto.
apply (eqTerm_trans _ _ _ _ _ _ _ _ _ cs n) with (multTerm (A:=A) multA (n:=n) (T1 A1 n) a0); auto.
apply (eqTerm_sym _ _ _ _ _ _ _ _ _ cs n); auto.
apply divP_eqT with (1 := cs) (a := a); auto.
apply (eqT_trans A n) with (multTerm (A:=A) multA (n:=n) (T1 A1 n) a); auto.
apply (eqTerm_imp_eqT A eqA n); auto.
apply nzeroP_comp_eqTerm with (1 := cs) (a := invTerm (A:=A) invA (n:=n) a); auto.
apply nZero_invTerm_nZero with (1 := cs); auto.
apply canonical_nzeroP with (ltM := ltM) (p := p0); auto.
apply (eqTerm_trans _ _ _ _ _ _ _ _ _ cs n) with (invTerm (A:=A) invA (n:=n) (multTerm (A:=A) multA (n:=n) (T1 A1 n) a)); auto.
apply (eqTerm_sym _ _ _ _ _ _ _ _ _ cs n); auto.
apply eqp_spminusf_com with (1 := cs); auto.
rewrite pX_invr with (1 := H'3); auto.
apply (eqp_trans _ _ _ _ _ _ _ _ _ cs n) with (y := mults (A:=A) multA (n:=n) (multTerm (A:=A) multA (n:=n) (invTerm (A:=A) invA (n:=n) (T1 A1 n)) (invTerm (A:=A) invA (n:=n) (T1 A1 n))) l); auto.
apply (eqp_sym _ _ _ _ _ _ _ _ _ cs n); auto.
apply mults_comp with (1 := cs); auto.
apply divP_eqT with (1 := cs) (a := a); auto.
rewrite pX_invl with (1 := H'3); auto.
apply (eqT_sym A n); apply (eqT_trans A n) with (y := multTerm (A:=A) multA (n:=n) (T1 A1 n) a0); auto.
apply (eqTerm_imp_eqT A eqA n); auto.
apply nzeroP_comp_eqTerm with (1 := cs) (a := invTerm (A:=A) invA (n:=n) a); auto.
apply nZero_invTerm_nZero with (1 := cs); auto.
apply canonical_nzeroP with (ltM := ltM) (p := p0); auto.
rewrite pX_invl with (1 := H'3); auto.
apply (eqTerm_trans _ _ _ _ _ _ _ _ _ cs n) with (multTerm (A:=A) multA (n:=n) (invTerm (A:=A) invA (n:=n) (invTerm (A:=A) invA (n:=n) (T1 A1 n))) a0); auto.
apply (eqTerm_sym _ _ _ _ _ _ _ _ _ cs n); apply mult_invTerm_com with (1 := cs); auto.
apply (eqTerm_trans _ _ _ _ _ _ _ _ _ cs n) with (multTerm (A:=A) multA (n:=n) (T1 A1 n) a0); apply (eqTerm_sym _ _ _ _ _ _ _ _ _ cs n); auto.
Admitted.

Theorem reduce_mults_invr : forall (Q : list (poly A0 eqA ltM)) (p q : list (Term A n)), reduce Q (mults (A:=A) multA (n:=n) (invTerm (A:=A) invA (n:=n) (T1 A1 n)) p) q -> canonical A0 eqA ltM p -> reduce Q p (mults (A:=A) multA (n:=n) (invTerm (A:=A) invA (n:=n) (T1 A1 n)) q).
intros Q p q H' H'0.
Admitted.

Lemma irreducible_inv_px_l : forall (Q : list (poly A0 eqA ltM)) (a : Term A n) (p : list (Term A n)), canonical A0 eqA ltM (pX a p) -> irreducible Q (pX a p) -> irreducible Q (pX a (pO A n)).
unfold irreducible in |- *.
intros Q a p H' H'0 q; red in |- *; intros H'1.
inversion_clear H'1.
apply H'0 with (q := spminusf A A0 A1 eqA invA minusA multA divA eqA_dec n ltM ltM_dec a b nZb p q0); auto.
Admitted.

Lemma pO_irreducible : forall Q : list (poly A0 eqA ltM), irreducible Q (pO A n).
unfold irreducible in |- *; auto.
Admitted.

Theorem irreducible_eqp_com : forall (Q : list (poly A0 eqA ltM)) (p q : list (Term A n)), irreducible Q p -> canonical A0 eqA ltM p -> eqP A eqA n p q -> irreducible Q q.
unfold irreducible in |- *.
intros Q p q H' H'0 H'1 q0; red in |- *; intros H'2.
apply H' with (q := q0); auto.
apply reduce_eqp_com with (p := q) (q := q0); auto.
apply eqp_imp_canonical with (1 := cs) (p := p); auto.
Admitted.

Lemma pickin_is_pX : forall (a : Term A n) (p : list (Term A n)) (Q : list (poly A0 eqA ltM)), pickinSetp a p Q -> exists b : Term A n, (exists q : list (Term A n), p = pX b q).
intros a p Q H'; elim H'; auto.
Admitted.

Lemma pick_inv_in : forall (Q : list (poly A0 eqA ltM)) (a : Term A n) (p : list (Term A n)), pickinSetp a p Q -> inPolySet p Q.
Admitted.

Lemma pick_inv_eqT_lem : forall (Q : list (poly A0 eqA ltM)) (a : Term A n) (p : list (Term A n)), pickinSetp a p Q -> forall (b : Term A n) (q : list (Term A n)), p = pX b q -> divP A A0 eqA multA divA n a b.
intros Q a p H'; elim H'; auto.
intros a0 b p0 H'0 H'1 H'2 b0 q H'3; injection H'3; auto.
Admitted.

Lemma pick_inv_eqT : forall (Q : list (poly A0 eqA ltM)) (a b : Term A n) (p q : list (Term A n)), pickinSetp a (pX b q) Q -> divP A A0 eqA multA divA n a b.
intros Q a b H' q H'0.
Admitted.

Theorem reducehead_imp_reduce : forall (Q : list (poly A0 eqA ltM)) (p q : list (Term A n)), reducehead Q p q -> reduce Q p q.
intros Q p q H'; elim H'; auto.
intros a b nZb p0 q0 H'0.
apply reducetop with (b := b) (nZb := nZb) (q := q0); auto.
apply pick_inv_in with (a := a); auto.
Admitted.

Theorem In_inp_inPolySet : forall (Q : list (poly A0 eqA ltM)) (p : poly A0 eqA ltM), In p Q -> ~ eqP A eqA n (s2p p) (pO A n) -> inPolySet (s2p p) Q.
intros Q; elim Q; simpl in |- *; auto.
intros p H'; elim H'.
intros a l H' p H'0; elim H'0; [ intros H'1; rewrite H'1; clear H'0 | intros H'1; clear H'0 ]; auto.
case p; simpl in |- *; auto.
intros x; case x; simpl in |- *; auto.
intros c H'0; elim H'0; auto.
Admitted.

Theorem in_inPolySet : forall (P : list (poly A0 eqA ltM)) (p : poly A0 eqA ltM), In p P -> ~ eqP A eqA n (s2p p) (pO A n) -> inPolySet (s2p p) P.
intros P; elim P; auto.
intros p H'; inversion H'.
simpl in |- *.
intros a l H' p H'0; elim H'0; [ intros H'1; rewrite <- H'1; clear H'0 | intros H'1; clear H'0 ]; auto.
case a; simpl in |- *.
intros x; case x; auto.
intros c H'0; elim H'0; auto.
Admitted.

Theorem inPolySet_inv0 : forall (P : list (poly A0 eqA ltM)) (p : list (Term A n)), inPolySet p P -> ~ eqP A eqA n p (pO A n).
intros P p H'; elim H'; auto.
Admitted.

Theorem inPolySet_inv1 : forall (P : list (poly A0 eqA ltM)) (p : list (Term A n)), inPolySet p P -> exists q : poly A0 eqA ltM, In q P /\ p = s2p q.
intros P p H'; elim H'; auto.
intros a p0 H P0.
exists (exist (canonical A0 eqA ltM) (a :: p0) H); split; simpl in |- *; auto.
intros a p0 P0 H'0 H'1; elim H'1; intros q E; elim E; intros H'2 H'3; clear E H'1.
Admitted.

Theorem Incl_inp_inPolySet : forall P Q : list (poly A0 eqA ltM), incl P Q -> forall p : list (Term A n), inPolySet p P -> inPolySet p Q.
intros P Q H' p H'0; auto.
elim (inPolySet_inv1 P p); [ intros q E; elim E; intros H'4 H'5; clear E | idtac ]; auto.
rewrite H'5.
apply in_inPolySet; auto.
rewrite <- H'5; auto.
Admitted.

Definition s2p : poly A0 eqA ltM -> list (Term A n).
intros H'; elim H'.
intros x H'0; exact x.
