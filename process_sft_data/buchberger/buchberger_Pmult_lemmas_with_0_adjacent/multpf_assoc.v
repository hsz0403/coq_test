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

Theorem multpf_assoc : forall p q r : list (Term A n), canonical A0 eqA ltM p -> canonical A0 eqA ltM q -> canonical A0 eqA ltM r -> eqP A eqA n (multpf p (multpf q r)) (multpf (multpf p q) r).
intros p q r; elim p; simpl in |- *; auto.
intros a l H' H'0 H'1 H'2.
cut (~ zeroP (A:=A) A0 eqA (n:=n) a); [ intros nZ0 | apply canonical_nzeroP with (ltM := ltM) (p := l) ]; auto.
cut (canonical A0 eqA ltM l); [ intros Op0 | apply canonical_imp_canonical with (a := a) ]; auto.
apply (eqp_trans _ _ _ _ _ _ _ _ _ cs n) with (y := pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec (multpf (mults (A:=A) multA (n:=n) a q) r) (multpf (multpf l q) r)); auto.
apply eqp_pluspf_com with (1 := cs); auto.
apply multpf_smultm_assoc; auto.
apply (eqp_sym _ _ _ _ _ _ _ _ _ cs n); auto.
apply multpf_dist_plusr; auto.
