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

Theorem spoly_Reducestar_pO : forall (Q : list (poly A0 eqA ltM)) (a b : Term A n), eqT (ppc (A:=A) A1 (n:=n) a b) (multTerm (A:=A) multA (n:=n) a b) -> forall (p q : list (Term A n)) (Cpxb : canonical A0 eqA ltM (pX b q)) (Cpxa : canonical A0 eqA ltM (pX a p)), inPolySet A A0 eqA n ltM (pX b q) Q -> inPolySet A A0 eqA n ltM (pX a p) Q -> reduceplus A A0 A1 eqA invA minusA multA divA eqA_dec n ltM ltM_dec Q (spolyf A A0 A1 eqA invA minusA multA divA eqA_dec n ltM ltM_dec (pX a p) (pX b q) Cpxa Cpxb) (pO A n).
intros Q a b H' p q Cpxb Cpxa H'0 H'1.
cut (canonical A0 eqA ltM p); [ intros Op2 | apply canonical_imp_canonical with (a := a) ]; auto.
cut (canonical A0 eqA ltM q); [ intros Op3 | apply canonical_imp_canonical with (a := b) ]; auto.
cut (~ zeroP (A:=A) A0 eqA (n:=n) a); [ intros nZa | idtac ]; auto.
cut (~ zeroP (A:=A) A0 eqA (n:=n) b); [ intros nZb | idtac ]; auto.
cut (~ zeroP (A:=A) A0 eqA (n:=n) (ppc (A:=A) A1 (n:=n) a b)); [ intros nZppab | idtac ]; auto.
apply reduceplus_mults_inv with (a := divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n) (multTerm (A:=A) multA (n:=n) a b) (b:= ppc (A:=A) A1 (n:=n) a b) nZppab) (1 := cs); auto.
apply divP_on_eqT_eqT; auto.
apply (eqT_sym A n); auto.
2: apply spolyf_canonical with (1 := cs); auto.
2: apply canonical_nzeroP with (ltM := ltM) (p := q); auto.
2: apply canonical_nzeroP with (ltM := ltM) (p := p); auto.
apply reduceplus_eqp_com with (1 := cs) (p := minuspf A A0 A1 eqA invA minusA multA eqA_dec n ltM ltM_dec (mults (A:=A) multA (n:=n) b p) (mults (A:=A) multA (n:=n) a q)) (q := pO A n); auto.
apply fspoly_Reduceplus_pO; auto.
apply (eqp_trans _ _ _ _ _ _ _ _ _ cs n) with (y := mults (A:=A) multA (n:=n) (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n) (multTerm (A:=A) multA (n:=n) a b) (b:=ppc (A:=A) A1 (n:=n) a b) nZppab) (minuspf A A0 A1 eqA invA minusA multA eqA_dec n ltM ltM_dec (mults (A:=A) multA (n:=n) (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n) (ppc (A:=A) A1 (n:=n) a b) (b:=a) nZa) p) (mults (A:=A) multA (n:=n) (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n) (ppc (A:=A) A1 (n:=n) a b) (b:=b) nZb) q))); auto.
apply (eqp_trans _ _ _ _ _ _ _ _ _ cs n) with (y := minuspf A A0 A1 eqA invA minusA multA eqA_dec n ltM ltM_dec (mults (A:=A) multA (n:=n) (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n) (multTerm (A:=A) multA (n:=n) a b) (b:=ppc (A:=A) A1 (n:=n) a b) nZppab) (mults (A:=A) multA (n:=n) (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n) (ppc (A:=A) A1 (n:=n) a b) (b:=a) nZa) p)) (mults (A:=A) multA (n:=n) (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n) (multTerm (A:=A) multA (n:=n) a b) (b:=ppc (A:=A) A1 (n:=n) a b) nZppab) (mults (A:=A) multA (n:=n) (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n) (ppc (A:=A) A1 (n:=n) a b) (b:=b) nZb) q))); auto.
apply (eqp_trans _ _ _ _ _ _ _ _ _ cs n) with (y := minuspf A A0 A1 eqA invA minusA multA eqA_dec n ltM ltM_dec (mults (A:=A) multA (n:=n) (multTerm (A:=A) multA (n:=n) (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n) (multTerm (A:=A) multA (n:=n) a b) (b:=ppc (A:=A) A1 (n:=n) a b) nZppab) (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n) (ppc (A:=A) A1 (n:=n) a b) (b:=a) nZa)) p) (mults (A:=A) multA (n:=n) (multTerm (A:=A) multA (n:=n) (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n) (multTerm (A:=A) multA (n:=n) a b) (b:=ppc (A:=A) A1 (n:=n) a b) nZppab) (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n) (ppc (A:=A) A1 (n:=n) a b) (b:=b) nZb)) q)); auto.
apply minuspf_comp with (1 := cs); auto.
apply mults_comp with (1 := cs); auto.
apply divP_comp_ppc0 with (1 := cs); auto.
apply mults_comp with (1 := cs); auto.
apply divP_comp_ppc1 with (1 := cs); auto.
apply minuspf_comp with (1 := cs); auto.
apply (eqp_sym _ _ _ _ _ _ _ _ _ cs n); auto.
apply (eqp_sym _ _ _ _ _ _ _ _ _ cs n); apply mults_comp_minuspf with (1 := cs); auto.
apply mults_comp with (1 := cs); auto.
apply (eqp_sym _ _ _ _ _ _ _ _ _ cs n); apply spolyf_def with (1 := cs); auto.
