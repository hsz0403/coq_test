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

Theorem multpf_smultm_assoc : forall (p q : list (Term A n)) (a : Term A n), canonical A0 eqA ltM p -> canonical A0 eqA ltM q -> ~ zeroP (A:=A) A0 eqA (n:=n) a -> eqP A eqA n (mults (A:=A) multA (n:=n) a (multpf p q)) (multpf (mults (A:=A) multA (n:=n) a p) q).
intros p q a; elim p; simpl in |- *; auto.
intros a0 l H' H'0 H'1 H'2.
cut (~ zeroP (A:=A) A0 eqA (n:=n) a0); [ intros nZ0 | apply canonical_nzeroP with (ltM := ltM) (p := l) ]; auto.
cut (canonical A0 eqA ltM l); [ intros Op0 | apply canonical_imp_canonical with (a := a0) ]; auto.
apply (eqp_trans _ _ _ _ _ _ _ _ _ cs n) with (y := pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec (mults (A:=A) multA (n:=n) a (mults (A:=A) multA (n:=n) a0 q)) (mults (A:=A) multA (n:=n) a (multpf l q))); auto.
apply eqp_pluspf_com with (1 := cs); auto.
apply (eqp_sym _ _ _ _ _ _ _ _ _ cs n); auto.
