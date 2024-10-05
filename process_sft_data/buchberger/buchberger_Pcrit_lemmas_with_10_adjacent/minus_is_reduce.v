Require Export Pspoly.
Require Export Pmult.
Section crit.
Load hCoefStructure.
Load hOrderStructure.
Load hSpoly.
Load hMult.
Definition Rminus : forall (a : Term A n) (nZa : ~ zeroP (A:=A) A0 eqA (n:=n) a), list (Term A n) -> list (Term A n) -> list (Term A n) -> list (Term A n).
intros a nZa p q r; elim r; clear r.
exact p.
intros b r Rec; exact (minuspf A A0 A1 eqA invA minusA multA eqA_dec n ltM ltM_dec Rec (mults (A:=A) multA (n:=n) (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n) b (b:=a) nZa) q)).
Defined.
Definition divPp : Term A n -> list (Term A n) -> Prop.
intros a p; elim p; clear p.
exact True.
intros b p Rec; exact (divP A A0 eqA multA divA n b a /\ Rec).
Defined.
Hint Resolve divP_inv3 : core.
Hint Resolve divP_inv3 : core.
Definition divpf : forall (a : Term A n) (nZa : ~ zeroP (A:=A) A0 eqA (n:=n) a), list (Term A n) -> list (Term A n).
intros a nZa p; elim p; clear p.
exact (pO A n).
intros b p Rec; exact (pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec (pX (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n) b (b:=a) nZa) (pO A n)) Rec).
Defined.
Hint Resolve divpf_canonical : core.
Hint Resolve canonical_Rminus : core.
Definition Dmult : forall (a : Term A n) (nZa : ~ zeroP (A:=A) A0 eqA (n:=n) a), list (Term A n) -> list (Term A n) -> list (Term A n).
intros a nZa p q; elim p; clear p.
exact (pO A n).
intros a1 p1 rec; exact (pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec (divpf a nZa (mults (A:=A) multA (n:=n) a1 q)) rec).
Defined.
Hint Resolve canonical_Dmult : core.
End crit.

Definition Rminus : forall (a : Term A n) (nZa : ~ zeroP (A:=A) A0 eqA (n:=n) a), list (Term A n) -> list (Term A n) -> list (Term A n) -> list (Term A n).
intros a nZa p q r; elim r; clear r.
exact p.
Admitted.

Theorem minuspf_in : forall (p q : list (Term A n)) (a b : Term A n), In a p -> ltT ltM b a -> canonical A0 eqA ltM p -> canonical A0 eqA ltM (pX b q) -> In a (minuspf A A0 A1 eqA invA minusA multA eqA_dec n ltM ltM_dec p (pX b q)).
intros p; elim p; simpl in |- *; auto.
intros q a b H'; elim H'; auto.
intros a l H' q a0 b H'0 H'1 H'2 H'3.
elim H'0; [ intros H'4; rewrite H'4; clear H'0 | intros H'4; clear H'0 ].
change (In a0 (minuspf A A0 A1 eqA invA minusA multA eqA_dec n ltM ltM_dec (pX a0 l) (pX b q))) in |- *.
rewrite <- minuspf_inv1_eq; simpl in |- *; auto.
case (ltT_dec A n ltM ltM_dec a b); intros test; [ case test; clear test; intros test | idtac ].
absurd (ltT ltM b a0); auto.
apply ltT_not_ltT; auto.
generalize H'4 H'2; elim l; simpl in |- *; auto.
intros H'0; elim H'0; auto.
intros a1 l0 H'0 H'5; elim H'5; [ intros H'6; rewrite <- H'6; clear H'5 | intros H'6; clear H'5 ]; auto.
intros H'5; apply (ltT_trans A n ltM os) with (y := a); auto.
apply (canonical_pX_order A A0 eqA) with (l := l0); auto.
intros H'5; apply H'0; auto.
change (canonical A0 eqA ltM (pX a l0)) in |- *.
apply canonical_skip_fst with (b := a1); auto.
change (In a0 (minuspf A A0 A1 eqA invA minusA multA eqA_dec n ltM ltM_dec (pX a l) (pX b q))) in |- *.
rewrite <- minuspf_inv1_eq; simpl in |- *; auto.
right; auto.
apply H'; auto.
apply canonical_imp_canonical with (a := a); auto.
absurd (ltT ltM b a0); auto.
apply ltT_not_ltT; auto.
apply eqT_compat_ltTr with (b := a); auto.
generalize H'4 H'2; elim l; simpl in |- *; auto.
intros H'0; elim H'0; auto.
intros a1 l0 H'0 H'5; elim H'5; [ intros H'6; rewrite <- H'6; clear H'5 | intros H'6; clear H'5 ]; auto.
intros H'5; apply (canonical_pX_order A A0 eqA) with (l := l0); auto.
intros H'5; apply H'0; auto.
change (canonical A0 eqA ltM (pX a l0)) in |- *.
Admitted.

Definition divPp : Term A n -> list (Term A n) -> Prop.
intros a p; elim p; clear p.
exact True.
Admitted.

Definition divpf : forall (a : Term A n) (nZa : ~ zeroP (A:=A) A0 eqA (n:=n) a), list (Term A n) -> list (Term A n).
intros a nZa p; elim p; clear p.
exact (pO A n).
Admitted.

Theorem divpf_canonical : forall (a : Term A n) (p : list (Term A n)) (nZa : ~ zeroP (A:=A) A0 eqA (n:=n) a), canonical A0 eqA ltM p -> canonical A0 eqA ltM (divpf a nZa p).
intros a p; elim p; simpl in |- *; auto.
intros a0 l H' H'0 H'1.
apply canonical_pluspf; auto.
apply canonicalp1; auto.
cut (~ zeroP (A:=A) A0 eqA (n:=n) a0); auto.
apply (canonical_nzeroP A A0 eqA n ltM) with (p := l); auto.
apply H'; auto.
Admitted.

Theorem divPp_divpf : forall (a : Term A n) (nZa : ~ zeroP (A:=A) A0 eqA (n:=n) a) (p : list (Term A n)), canonical A0 eqA ltM p -> divPp a p -> eqP A eqA n p (mults (A:=A) multA (n:=n) a (divpf a nZa p)).
intros a nZa p; elim p; simpl in |- *; auto.
intros a0 l H' H'0 H'1; elim H'1; intros H'2 H'3; clear H'1.
cut (canonical A0 eqA ltM l); [ intros Op0 | apply canonical_imp_canonical with (a := a0) ]; auto.
apply (eqp_trans _ _ _ _ _ _ _ _ _ cs n) with (y := pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec (mults (A:=A) multA (n:=n) a (pX (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n) a0 (b:=a) nZa) (pO A n))) (mults (A:=A) multA (n:=n) a (divpf a nZa l))).
2: apply (eqp_sym _ _ _ _ _ _ _ _ _ cs n); auto.
apply (eqp_trans _ _ _ _ _ _ _ _ _ cs n) with (y := pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec (mults (A:=A) multA (n:=n) a (pX (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n) a0 (b:=a) nZa) (pO A n))) l).
simpl in |- *.
apply (eqp_trans _ _ _ _ _ _ _ _ _ cs n) with (y := pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec (pX (multTerm (A:=A) multA (n:=n) (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n) a0 (b:=a) nZa) a) (pO A n)) l).
apply (eqp_trans _ _ _ _ _ _ _ _ _ cs n) with (y := pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec (pX a0 (pO A n)) l).
change (eqP A eqA n (pX a0 l) (pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec (pX a0 (pO A n)) l)) in |- *; auto.
apply (eqp_trans _ _ _ _ _ _ _ _ _ cs n) with (y := pX a0 (pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec (pO A n) l)).
apply (eqp_sym _ _ _ _ _ _ _ _ _ cs n); auto.
rewrite pluspf_inv1_eqa; auto.
apply canonicalp1; auto.
apply (canonical_nzeroP A A0 eqA n ltM) with (p := l); auto.
inversion H'2; auto.
auto.
Admitted.

Theorem canonical_Rminus : forall (r p q : list (Term A n)) (a : Term A n) (nZa : ~ zeroP (A:=A) A0 eqA (n:=n) a), canonical A0 eqA ltM p -> canonical A0 eqA ltM q -> canonical A0 eqA ltM r -> canonical A0 eqA ltM (Rminus a nZa p q r).
intros r; elim r; simpl in |- *; auto.
intros a l nZa p q a0 H'0 H'1 H'2 H'3.
cut (canonical A0 eqA ltM l); [ idtac | apply canonical_imp_canonical with (a := a); auto ]; auto.
Admitted.

Theorem Rminus_in : forall (r p q : list (Term A n)) (a b : Term A n) (nZb : ~ zeroP (A:=A) A0 eqA (n:=n) b), divPp b r -> In a p -> canonical A0 eqA ltM p -> canonical A0 eqA ltM (pX b q) -> canonical A0 eqA ltM (pX a r) -> In a (Rminus b nZb p (pX b q) r).
intros r; elim r; simpl in |- *; auto.
intros a l H' p q a0 b nZb H'0 H'1 H'2 H'3 H'4.
cut (~ zeroP (A:=A) A0 eqA (n:=n) b); [ intros Z1 | apply canonical_nzeroP with (ltM := ltM) (p := q); auto ].
elim H'0; intros H'6 H'7; clear H'0.
apply minuspf_in; auto.
apply H'; auto.
apply canonical_skip_fst with (b := a); auto.
apply eqT_compat_ltTl with (b := a); auto.
apply (eqTerm_imp_eqT A eqA n); auto.
inversion H'6; auto.
apply (canonical_pX_order A A0 eqA) with (l := l); auto.
apply canonical_Rminus; auto.
apply canonical_imp_canonical with (a := a); auto.
apply canonical_imp_canonical with (a := a0); auto.
Admitted.

Theorem Rminus_is_reduceplus : forall (Q : list (poly A0 eqA ltM)) (a : Term A n) (q : list (Term A n)) (nZa : ~ zeroP (A:=A) A0 eqA (n:=n) a), canonical A0 eqA ltM q -> inPolySet A A0 eqA n ltM (pX a q) Q -> forall r : list (Term A n), canonical A0 eqA ltM r -> divPp a r -> forall p : list (Term A n), canonical A0 eqA ltM p -> incl r p -> reduceplus A A0 A1 eqA invA minusA multA divA eqA_dec n ltM ltM_dec Q p (Rminus a nZa p (pX a q) r).
intros Q a q nZa Op0 in0 r; elim r; clear r.
simpl in |- *; intros H' H'0 p H'1 H'2; auto.
apply Rstar_0; auto.
intros a0 r1 Rec Op1 divp0 p Op2 incl0.
cut (canonical A0 eqA ltM r1); [ intros Cr1 | apply canonical_imp_canonical with (a := a0); auto ].
cut (canonical A0 eqA ltM (pX a q)); [ intros Caq | apply inPolySet_imp_canonical with (L := Q); auto ].
elim divp0; intros H' H'0; clear divp0.
apply reduceplus_trans with (1 := cs) (y := Rminus a nZa p (pX a q) r1); auto.
apply Rec; auto.
red in |- *; intros p' H; apply incl0; auto with datatypes.
apply reduceplus_eqp_com with (1 := cs) (p := Rminus a nZa p (pX a q) r1) (q := minuspf A A0 A1 eqA invA minusA multA eqA_dec n ltM ltM_dec (Rminus a nZa p (pX a q) r1) (mults (A:=A) multA (n:=n) (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n) a0 (b:=a) nZa) (pX a q))); auto.
apply reduce_imp_reduceplus with (1 := cs); auto.
apply minus_is_reduce; auto.
Admitted.

Definition Dmult : forall (a : Term A n) (nZa : ~ zeroP (A:=A) A0 eqA (n:=n) a), list (Term A n) -> list (Term A n) -> list (Term A n).
intros a nZa p q; elim p; clear p.
exact (pO A n).
Admitted.

Theorem canonical_Dmult : forall (a : Term A n) (nZa : ~ zeroP (A:=A) A0 eqA (n:=n) a) (p q : list (Term A n)), canonical A0 eqA ltM p -> canonical A0 eqA ltM q -> canonical A0 eqA ltM (Dmult a nZa p q).
intros a nZa p; elim p; simpl in |- *; auto.
intros a0 l H' q H'0 H'1.
cut (canonical A0 eqA ltM l); [ idtac | apply canonical_imp_canonical with (a := a0); auto ].
cut (~ zeroP (A:=A) A0 eqA (n:=n) a0); auto.
Admitted.

Theorem divp_is_multTerm : forall (a b : Term A n) (nZb : ~ zeroP (A:=A) A0 eqA (n:=n) b), divP A A0 eqA multA divA n a b -> forall p : list (Term A n), canonical A0 eqA ltM p -> eqP A eqA n (mults (A:=A) multA (n:=n) (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n) a (b:=b) nZb) p) (divpf b nZb (mults (A:=A) multA (n:=n) a p)).
intros a b nZb H'; inversion H'.
intros p; elim p; simpl in |- *; auto.
intros a1 p1 H'0 H'1.
cut (canonical A0 eqA ltM p1); [ intros Op0 | apply canonical_imp_canonical with (a := a1) ]; auto.
cut (~ zeroP (A:=A) A0 eqA (n:=n) a1); [ intros Z0 | apply canonical_nzeroP with (ltM := ltM) (p := p1) ]; auto.
apply (eqp_trans _ _ _ _ _ _ _ _ _ cs n) with (y := pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec (pX (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n) (multTerm (A:=A) multA (n:=n) a a1) (b:=b) nZb) (pO A n)) (mults (A:=A) multA (n:=n) (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n) a (b:=b) nZb) p1)); auto.
cut (eqTerm (A:=A) eqA (n:=n) (multTerm (A:=A) multA (n:=n) (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n) a (b:=b) nZb) a1) (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n) (multTerm (A:=A) multA (n:=n) a a1) (b:=b) nZb)); auto.
intros H'2.
apply (eqp_trans _ _ _ _ _ _ _ _ _ cs n) with (y := pX (multTerm (A:=A) multA (n:=n) (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n) a (b:=b) nZb) a1) (pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec (pO A n) (mults (A:=A) multA (n:=n) (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n) a (b:=b) nZb) p1))); auto.
apply (eqp_sym _ _ _ _ _ _ _ _ _ cs n); auto.
rewrite pluspf_inv1_eqa; auto.
change (canonical A0 eqA ltM (mults (A:=A) multA (n:=n) (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n) a (b:=b) nZb) (pX a1 p1))) in |- *; auto.
Admitted.

Theorem minus_is_reduce : forall (Q : list (poly A0 eqA ltM)) (a : Term A n) (nZa : ~ zeroP (A:=A) A0 eqA (n:=n) a) (q : list (Term A n)), inPolySet A A0 eqA n ltM (pX a q) Q -> forall u : Term A n, divP A A0 eqA multA divA n u a -> forall p : list (Term A n), canonical A0 eqA ltM p -> In u p -> reduce A A0 A1 eqA invA minusA multA divA eqA_dec n ltM ltM_dec Q p (minuspf A A0 A1 eqA invA minusA multA eqA_dec n ltM ltM_dec p (mults (A:=A) multA (n:=n) (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n) u (b:=a) nZa) (pX a q))).
intros Q a nZa q inP0 u divP0 p; elim p.
intros H' H'0; elim H'0; auto.
intros a0 l H' H'0 H'1; elim H'1; [ intros H'2; rewrite H'2; clear H'1 | intros H'2; clear H'1 ]; auto.
change (reduce A A0 A1 eqA invA minusA multA divA eqA_dec n ltM ltM_dec Q (pX u l) (minuspf A A0 A1 eqA invA minusA multA eqA_dec n ltM ltM_dec (pX u l) (mults (A:=A) multA (n:=n) (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n) u (b:=a) nZa) (pX a q)))) in |- *.
apply reducetop with (b := a) (nZb := nZa) (q := q); auto.
apply (eqp_trans _ _ _ _ _ _ _ _ _ cs n) with (y := spminusf A A0 A1 eqA invA minusA multA divA eqA_dec n ltM ltM_dec u a nZa (pX u l) (pX a q)); auto.
apply spminusf_extend with (1 := cs); auto.
rewrite <- H'2; auto.
apply inPolySet_imp_canonical with (L := Q); auto.
apply reduce_eqp_com with (1 := cs) (p := pX a0 l) (q := pX a0 (minuspf A A0 A1 eqA invA minusA multA eqA_dec n ltM ltM_dec l (mults (A:=A) multA (n:=n) (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n) u (b:=a) nZa) (pX a q)))); auto.
apply reduceskip; auto.
apply H'; auto.
apply canonical_imp_canonical with (a := a0); auto.
change (eqP A eqA n (pX a0 (minuspf A A0 A1 eqA invA minusA multA eqA_dec n ltM ltM_dec l (mults (A:=A) multA (n:=n) (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n) u (b:=a) nZa) (pX a q)))) (minuspf A A0 A1 eqA invA minusA multA eqA_dec n ltM ltM_dec (pX a0 l) (mults (A:=A) multA (n:=n) (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n) u (b:=a) nZa) (pX a q)))) in |- *.
simpl in |- *; apply minuspf_inv1 with (1 := cs); auto.
apply eqT_compat_ltTl with (b := u); auto.
inversion divP0; auto.
apply (eqTerm_imp_eqT A eqA n); auto.
generalize H'2 H'0; elim l; simpl in |- *; auto.
intros H'1; elim H'1; auto.
intros a2 l0 H'1 H'3; elim H'3; [ intros H'4; rewrite <- H'4; clear H'3 | intros H'4; clear H'3 ]; auto.
intros H'5.
apply (canonical_pX_order A A0 eqA) with (l := l0); auto.
intros H'5; apply H'1; auto.
change (canonical A0 eqA ltM (pX a0 l0)) in |- *.
apply canonical_skip_fst with (b := a2); auto.
