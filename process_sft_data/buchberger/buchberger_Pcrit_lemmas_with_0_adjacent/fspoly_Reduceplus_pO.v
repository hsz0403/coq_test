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

Theorem fspoly_Reduceplus_pO : forall (Q : list (poly A0 eqA ltM)) (a b : Term A n), eqT (ppc (A:=A) A1 (n:=n) a b) (multTerm (A:=A) multA (n:=n) a b) -> forall p q : list (Term A n), inPolySet A A0 eqA n ltM (pX b q) Q -> inPolySet A A0 eqA n ltM (pX a p) Q -> reduceplus A A0 A1 eqA invA minusA multA divA eqA_dec n ltM ltM_dec Q (minuspf A A0 A1 eqA invA minusA multA eqA_dec n ltM ltM_dec (mults (A:=A) multA (n:=n) b p) (mults (A:=A) multA (n:=n) a q)) (pO A n).
intros Q a b H' p q H'0 H'1.
cut (canonical A0 eqA ltM (pX a p)); [ intros Op0 | apply inPolySet_imp_canonical with (L := Q) ]; auto.
cut (canonical A0 eqA ltM (pX b q)); [ intros Op1 | apply inPolySet_imp_canonical with (L := Q) ]; auto.
cut (canonical A0 eqA ltM p); [ intros Op2 | apply canonical_imp_canonical with (a := a) ]; auto.
cut (canonical A0 eqA ltM q); [ intros Op3 | apply canonical_imp_canonical with (a := b) ]; auto.
cut (~ zeroP (A:=A) A0 eqA (n:=n) a); [ intros Z0 | apply canonical_nzeroP with (ltM := ltM) (p := p) ]; auto.
cut (~ zeroP (A:=A) A0 eqA (n:=n) b); [ intros Z1 | apply canonical_nzeroP with (ltM := ltM) (p := q) ]; auto.
apply reduceplus_trans with (1 := cs) (y := mults (A:=A) multA (n:=n) (invTerm (A:=A) invA (n:=n) (T1 A1 n)) (multpf A A0 eqA plusA multA eqA_dec n ltM ltM_dec (pX a p) q)); auto.
apply spoly_Reduce; auto.
apply reduceplus_eqp_com with (1 := cs) (p := mults (A:=A) multA (n:=n) (invTerm (A:=A) invA (n:=n) (T1 A1 n)) (multpf A A0 eqA plusA multA eqA_dec n ltM ltM_dec q (pX a p))) (q := mults (A:=A) multA (n:=n) (invTerm (A:=A) invA (n:=n) (T1 A1 n)) (pO A n)); auto.
apply reduceplus_mults with (1 := cs); auto.
apply spoly_reduceplus_pO; auto.
apply mults_comp with (1 := cs); auto.
apply multpf_com with (1 := cs); auto.
