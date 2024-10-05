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

Theorem canonical_multpf : forall l1 l2 : list (Term A n), canonical A0 eqA ltM l1 -> canonical A0 eqA ltM l2 -> canonical A0 eqA ltM (multpf l1 l2).
intros l1; elim l1; simpl in |- *; auto.
intros a l H' l2 H'0 H'1; try assumption.
apply canonical_pluspf; auto.
apply canonical_mults with (1 := cs); auto.
apply canonical_nzeroP with (ltM := ltM) (p := l); auto.
apply H'; auto.
apply canonical_imp_canonical with (a := a); auto.
