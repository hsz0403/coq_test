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

Theorem pluspf_pX : forall (p : list (Term A n)) (a : Term A n), canonical A0 eqA ltM (pX a p) -> eqP A eqA n (pX a p) (pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec (pX a (pO A n)) p).
intros p; case p; clear p; auto.
intros a H; change (eqP A eqA n (pX a (pO A n)) (pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec (pX a (pO A n)) (pO A n))) in |- *.
apply (eqp_sym _ _ _ _ _ _ _ _ _ cs n); auto.
intros a1 p a0 H'.
cut (canonical A0 eqA ltM (pX a1 p)); [ intros Op0 | apply canonical_imp_canonical with (a := a0) ]; auto.
apply (eqp_trans _ _ _ _ _ _ _ _ _ cs n) with (y := pX a0 (pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec (pO A n) (pX a1 p))); auto.
apply (eqp_sym _ _ _ _ _ _ _ _ _ cs n); auto.
change (eqP A eqA n (pX a0 (pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec (pO A n) (pX a1 p))) (pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec (pX a0 (pO A n)) (pX a1 p))) in |- *; auto.
apply pluspf_inv1 with (1 := cs); auto.
apply (canonical_pX_order _ A0 eqA) with (l := p); auto.
