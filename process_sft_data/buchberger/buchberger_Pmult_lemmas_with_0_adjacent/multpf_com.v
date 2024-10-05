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

Theorem multpf_com : forall p q : list (Term A n), canonical A0 eqA ltM p -> canonical A0 eqA ltM q -> eqP A eqA n (multpf p q) (multpf q p).
intros p; elim p; simpl in |- *; auto.
intros q; elim q; simpl in |- *; auto.
intros a l H' H'0 H'1.
cut (canonical A0 eqA ltM l); [ intros Op0 | apply canonical_imp_canonical with (a := a) ]; auto.
cut (~ zeroP (A:=A) A0 eqA (n:=n) a); [ intros Z0 | apply canonical_nzeroP with (ltM := ltM) (p := l) ]; auto.
apply (eqp_trans _ _ _ _ _ _ _ _ _ cs n) with (y := pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec (pO A n) (pO A n)); auto.
apply (eqp_sym _ _ _ _ _ _ _ _ _ cs n); auto.
intros a l H' q H'0 H'1.
cut (canonical A0 eqA ltM l); [ intros Op0 | apply canonical_imp_canonical with (a := a) ]; auto.
cut (~ zeroP (A:=A) A0 eqA (n:=n) a); [ intros Z0 | apply canonical_nzeroP with (ltM := ltM) (p := l) ]; auto.
apply (eqp_trans _ _ _ _ _ _ _ _ _ cs n) with (y := pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec (mults (A:=A) multA (n:=n) a q) (multpf q l)); auto.
apply (eqp_sym _ _ _ _ _ _ _ _ _ cs n); auto.
change (eqP A eqA n (multpf q (pX a l)) (pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec (mults (A:=A) multA (n:=n) a q) (multpf q l))) in |- *.
apply multpf_disr_pX; auto.
