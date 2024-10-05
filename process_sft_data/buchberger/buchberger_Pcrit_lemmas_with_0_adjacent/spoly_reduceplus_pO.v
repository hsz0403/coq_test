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

Theorem spoly_reduceplus_pO : forall (Q : list (poly A0 eqA ltM)) (p q : list (Term A n)), inPolySet A A0 eqA n ltM q Q -> canonical A0 eqA ltM p -> reduceplus A A0 A1 eqA invA minusA multA divA eqA_dec n ltM ltM_dec Q (multpf A A0 eqA plusA multA eqA_dec n ltM ltM_dec p q) (pO A n).
intros Q p; elim p; auto.
simpl in |- *; auto.
intros; apply Rstar_0; auto.
intros a1 p1 H' q H'0 H'1.
cut (canonical A0 eqA ltM p1); [ intros Op0 | apply canonical_imp_canonical with (a := a1) ]; auto.
cut (canonical A0 eqA ltM q); [ intros Op1 | apply inPolySet_imp_canonical with (L := Q) ]; auto.
cut (~ zeroP (A:=A) A0 eqA (n:=n) a1); [ intros Z0 | apply canonical_nzeroP with (ltM := ltM) (p := p1) ]; auto.
apply reduceplus_trans with (1 := cs) (y := multpf A A0 eqA plusA multA eqA_dec n ltM ltM_dec p1 q); auto.
generalize Op1 H'0; case q; clear Op1 H'0 q.
intros H'0 H'2; elim (not_nil_in_polySet A A0 eqA n ltM Q); auto.
intros b1 q1 H'0 H'2.
cut (canonical A0 eqA ltM q1); [ intros Op2 | apply canonical_imp_canonical with (a := b1) ]; auto.
cut (~ zeroP (A:=A) A0 eqA (n:=n) b1); [ intros nZb1 | apply canonical_nzeroP with (ltM := ltM) (p := q1) ]; auto.
apply reduceplus_eqp_com with (1 := cs) (p := multpf A A0 eqA plusA multA eqA_dec n ltM ltM_dec (pX a1 p1) (pX b1 q1)) (q := minuspf A A0 A1 eqA invA minusA multA eqA_dec n ltM ltM_dec (multpf A A0 eqA plusA multA eqA_dec n ltM ltM_dec (pX a1 p1) (pX b1 q1)) (mults (A:=A) multA (n:=n) (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n) (multTerm (A:=A) multA (n:=n) a1 b1) (b:=b1) nZb1) (pX b1 q1))); auto.
apply reduce_imp_reduceplus with (1 := cs); auto.
apply minus_is_reduce; auto.
apply in_multpf_head; auto.
cut (eqTerm (A:=A) eqA (n:=n) (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n) (multTerm (A:=A) multA (n:=n) a1 b1) (b:=b1) nZb1) a1); [ intros Eq0 | auto ].
apply (eqp_trans _ _ _ _ _ _ _ _ _ cs n) with (y := minuspf A A0 A1 eqA invA minusA multA eqA_dec n ltM ltM_dec (multpf A A0 eqA plusA multA eqA_dec n ltM ltM_dec (pX a1 p1) (pX b1 q1)) (mults (A:=A) multA (n:=n) a1 (pX b1 q1))); [ auto | idtac ].
apply (eqp_trans _ _ _ _ _ _ _ _ _ cs n) with (y := pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec (pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec (mults (A:=A) multA (n:=n) a1 (pX b1 q1)) (multpf A A0 eqA plusA multA eqA_dec n ltM ltM_dec p1 (pX b1 q1))) (mults (A:=A) multA (n:=n) (invTerm (A:=A) invA (n:=n) (T1 A1 n)) (mults (A:=A) multA (n:=n) a1 (pX b1 q1)))); [ auto | idtac ].
apply (eqp_trans _ _ _ _ _ _ _ _ _ cs n) with (y := pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec (pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec (multpf A A0 eqA plusA multA eqA_dec n ltM ltM_dec p1 (pX b1 q1)) (mults (A:=A) multA (n:=n) a1 (pX b1 q1))) (mults (A:=A) multA (n:=n) (invTerm (A:=A) invA (n:=n) (T1 A1 n)) (mults (A:=A) multA (n:=n) a1 (pX b1 q1)))); [ auto | idtac ].
apply (eqp_trans _ _ _ _ _ _ _ _ _ cs n) with (y := pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec (multpf A A0 eqA plusA multA eqA_dec n ltM ltM_dec p1 (pX b1 q1)) (pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec (mults (A:=A) multA (n:=n) a1 (pX b1 q1)) (mults (A:=A) multA (n:=n) (invTerm (A:=A) invA (n:=n) (T1 A1 n)) (mults (A:=A) multA (n:=n) a1 (pX b1 q1))))); [ auto | idtac ].
apply (eqp_trans _ _ _ _ _ _ _ _ _ cs n) with (y := pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec (multpf A A0 eqA plusA multA eqA_dec n ltM ltM_dec p1 (pX b1 q1)) (minuspf A A0 A1 eqA invA minusA multA eqA_dec n ltM ltM_dec (mults (A:=A) multA (n:=n) a1 (pX b1 q1)) (mults (A:=A) multA (n:=n) a1 (pX b1 q1)))).
apply (eqp_sym _ _ _ _ _ _ _ _ _ cs n); auto.
apply (eqp_trans _ _ _ _ _ _ _ _ _ cs n) with (y := pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec (multpf A A0 eqA plusA multA eqA_dec n ltM ltM_dec p1 (pX b1 q1)) (pO A n)); auto.
apply eqp_pluspf_com with (1 := cs); auto.
apply minuspf_refl with (1 := cs); auto.
apply (eqTerm_trans _ _ _ _ _ _ _ _ _ cs n) with (y := multTerm (A:=A) multA (n:=n) a1 (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n) b1 (b:=b1) nZb1)); auto.
apply (eqTerm_trans _ _ _ _ _ _ _ _ _ cs n) with (y := multTerm (A:=A) multA (n:=n) a1 (T1 A1 n)); auto.
apply (eqTerm_sym _ _ _ _ _ _ _ _ _ cs n); auto.
