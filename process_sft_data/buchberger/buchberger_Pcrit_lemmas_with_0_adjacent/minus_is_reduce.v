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
