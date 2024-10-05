Require Export Pmults.
Section Pmult.
Load hCoefStructure.
Load hOrderStructure.
Load hMults.
Fixpoint multpf (p : list (Term A n)) : list (Term A n) -> list (Term A n) := fun q : list (Term A n) => match p with | nil => pO A n | a :: p' => pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec (mults (A:=A) multA (n:=n) a q) (multpf p' q) end.
Hint Resolve canonical_multpf : core.
Definition smult : poly A0 eqA ltM -> poly A0 eqA ltM -> poly A0 eqA ltM.
intros sp1 sp2.
case sp1; case sp2.
intros p1 H'1 p2 H'2; exists (multpf p1 p2); auto.
Defined.
End Pmult.

Theorem multpf_disr_pX : forall (p q : list (Term A n)) (a : Term A n), canonical A0 eqA ltM p -> canonical A0 eqA ltM (pX a q) -> eqP A eqA n (multpf p (pX a q)) (pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec (mults (A:=A) multA (n:=n) a p) (multpf p q)).
intros p; elim p; clear p; simpl in |- *; auto.
intros; apply (eqp_sym _ _ _ _ _ _ _ _ _ cs n); auto.
intros b p Rec q a Op0 Op1.
cut (canonical A0 eqA ltM q); [ intros Op2 | apply canonical_imp_canonical with (a := a) ]; auto.
cut (canonical A0 eqA ltM p); [ intros Op3 | apply canonical_imp_canonical with (a := b) ]; auto.
cut (~ zeroP (A:=A) A0 eqA (n:=n) a); [ intros nZ0 | apply canonical_nzeroP with (ltM := ltM) (p := q) ]; auto.
cut (~ zeroP (A:=A) A0 eqA (n:=n) b); [ intros nZ1 | apply canonical_nzeroP with (ltM := ltM) (p := p) ]; auto.
cut (~ zeroP (A:=A) A0 eqA (n:=n) (multTerm (A:=A) multA (n:=n) b a)); [ intros nZ2 | idtac ]; auto.
cut (~ zeroP (A:=A) A0 eqA (n:=n) (multTerm (A:=A) multA (n:=n) a b)); [ intros nZ3 | idtac ]; auto.
apply (eqp_trans _ _ _ _ _ _ _ _ _ cs n) with (y := pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec (pX (multTerm (A:=A) multA (n:=n) b a) (mults (A:=A) multA (n:=n) b q)) (pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec (mults (A:=A) multA (n:=n) a p) (multpf p q))); auto.
apply eqp_pluspf_com with (1 := cs); auto.
change (canonical A0 eqA ltM (mults (A:=A) multA (n:=n) b (pX a q))) in |- *; auto.
change (canonical A0 eqA ltM (mults (A:=A) multA (n:=n) b (pX a q))) in |- *; auto.
apply (eqp_trans _ _ _ _ _ _ _ _ _ cs n) with (y := pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec (pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec (pX (multTerm (A:=A) multA (n:=n) b a) (pO A n)) (mults (A:=A) multA (n:=n) b q)) (pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec (mults (A:=A) multA (n:=n) a p) (multpf p q))); auto.
cut (canonical A0 eqA ltM (pX (multTerm (A:=A) multA (n:=n) b a) (mults (A:=A) multA (n:=n) b q))); [ intros Op4 | idtac ]; auto.
apply eqp_pluspf_com with (1 := cs); auto.
apply pluspf_pX; auto.
change (canonical A0 eqA ltM (mults (A:=A) multA (n:=n) b (pX a q))) in |- *; auto.
apply (eqp_trans _ _ _ _ _ _ _ _ _ cs n) with (y := pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec (pX (multTerm (A:=A) multA (n:=n) b a) (pO A n)) (pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec (mults (A:=A) multA (n:=n) b q) (pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec (mults (A:=A) multA (n:=n) a p) (multpf p q)))); auto.
apply (eqp_trans _ _ _ _ _ _ _ _ _ cs n) with (y := pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec (pX (multTerm (A:=A) multA (n:=n) b a) (pO A n)) (pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec (mults (A:=A) multA (n:=n) b q) (pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec (multpf p q) (mults (A:=A) multA (n:=n) a p)))); auto.
apply (eqp_trans _ _ _ _ _ _ _ _ _ cs n) with (y := pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec (pX (multTerm (A:=A) multA (n:=n) b a) (pO A n)) (pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec (pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec (mults (A:=A) multA (n:=n) b q) (multpf p q)) (mults (A:=A) multA (n:=n) a p))); auto.
apply (eqp_sym _ _ _ _ _ _ _ _ _ cs n); auto.
apply (eqp_trans _ _ _ _ _ _ _ _ _ cs n) with (y := pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec (pX (multTerm (A:=A) multA (n:=n) b a) (pO A n)) (pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec (mults (A:=A) multA (n:=n) a p) (pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec (mults (A:=A) multA (n:=n) b q) (multpf p q)))); auto.
apply (eqp_trans _ _ _ _ _ _ _ _ _ cs n) with (y := pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec (pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec (pX (multTerm (A:=A) multA (n:=n) b a) (pO A n)) (mults (A:=A) multA (n:=n) a p)) (pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec (mults (A:=A) multA (n:=n) b q) (multpf p q))); auto.
apply (eqp_sym _ _ _ _ _ _ _ _ _ cs n); auto.
apply eqp_pluspf_com with (1 := cs); auto.
change (canonical A0 eqA ltM (mults (A:=A) multA (n:=n) a (pX b p))) in |- *; auto.
apply (eqp_trans _ _ _ _ _ _ _ _ _ cs n) with (y := pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec (pX (multTerm (A:=A) multA (n:=n) a b) (pO A n)) (mults (A:=A) multA (n:=n) a p)); auto.
apply (eqp_sym _ _ _ _ _ _ _ _ _ cs n); auto.
apply pluspf_pX; auto.
change (canonical A0 eqA ltM (mults (A:=A) multA (n:=n) a (pX b p))) in |- *; auto.
