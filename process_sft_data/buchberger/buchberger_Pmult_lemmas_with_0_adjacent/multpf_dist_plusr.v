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

Theorem multpf_dist_plusr : forall (p q r : list (Term A n)) (a : Term A n), canonical A0 eqA ltM p -> canonical A0 eqA ltM q -> canonical A0 eqA ltM r -> eqP A eqA n (multpf (pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec p q) r) (pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec (multpf p r) (multpf q r)).
intros p q r; elim r.
intros H' H'0 H'1 H'2.
apply (eqp_trans _ _ _ _ _ _ _ _ _ cs n) with (y := multpf (pO A n) (pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec p q)); auto.
apply multpf_com; auto.
apply (eqp_trans _ _ _ _ _ _ _ _ _ cs n) with (y := pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec (multpf (pO A n) p) (multpf (pO A n) q)); auto.
simpl in |- *; apply (eqp_sym _ _ _ _ _ _ _ _ _ cs n); auto.
apply eqp_pluspf_com with (1 := cs); auto; apply multpf_com; auto.
intros a l H' H'0 H'1 H'2 H'3.
cut (~ zeroP (A:=A) A0 eqA (n:=n) a); [ intros nZ0 | apply canonical_nzeroP with (ltM := ltM) (p := l) ]; auto.
cut (canonical A0 eqA ltM l); [ intros Op0 | apply canonical_imp_canonical with (a := a) ]; auto.
apply (eqp_trans _ _ _ _ _ _ _ _ _ cs n) with (y := pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec (mults (A:=A) multA (n:=n) a (pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec p q)) (multpf (pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec p q) l)); auto.
change (eqP A eqA n (multpf (pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec p q) (pX a l)) (pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec (mults (A:=A) multA (n:=n) a (pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec p q)) (multpf (pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec p q) l))) in |- *.
apply multpf_disr_pX; auto.
apply (eqp_trans _ _ _ _ _ _ _ _ _ cs n) with (y := pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec (pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec (mults (A:=A) multA (n:=n) a p) (mults (A:=A) multA (n:=n) a q)) (pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec (multpf p l) (multpf q l))); auto.
apply (eqp_trans _ _ _ _ _ _ _ _ _ cs n) with (y := pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec (mults (A:=A) multA (n:=n) a p) (pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec (mults (A:=A) multA (n:=n) a q) (pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec (multpf p l) (multpf q l)))); auto.
apply (eqp_trans _ _ _ _ _ _ _ _ _ cs n) with (y := pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec (mults (A:=A) multA (n:=n) a p) (pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec (pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec (mults (A:=A) multA (n:=n) a q) (multpf p l)) (multpf q l))); auto.
apply (eqp_sym _ _ _ _ _ _ _ _ _ cs n); auto.
apply (eqp_trans _ _ _ _ _ _ _ _ _ cs n) with (y := pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec (mults (A:=A) multA (n:=n) a p) (pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec (pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec (multpf p l) (mults (A:=A) multA (n:=n) a q)) (multpf q l))); auto.
apply (eqp_trans _ _ _ _ _ _ _ _ _ cs n) with (y := pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec (mults (A:=A) multA (n:=n) a p) (pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec (multpf p l) (pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec (mults (A:=A) multA (n:=n) a q) (multpf q l)))); auto.
apply (eqp_trans _ _ _ _ _ _ _ _ _ cs n) with (y := pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec (pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec (mults (A:=A) multA (n:=n) a p) (multpf p l)) (pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec (mults (A:=A) multA (n:=n) a q) (multpf q l))); auto.
apply (eqp_sym _ _ _ _ _ _ _ _ _ cs n); auto.
apply eqp_pluspf_com with (1 := cs); auto.
change (eqP A eqA n (pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec (mults (A:=A) multA (n:=n) a p) (multpf p l)) (multpf p (pX a l))) in |- *.
apply (eqp_sym _ _ _ _ _ _ _ _ _ cs n); apply multpf_disr_pX; auto.
change (eqP A eqA n (pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec (mults (A:=A) multA (n:=n) a q) (multpf q l)) (multpf q (pX a l))) in |- *.
apply (eqp_sym _ _ _ _ _ _ _ _ _ cs n); apply multpf_disr_pX; auto.
