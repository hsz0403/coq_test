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

Theorem multpf_comp : forall p r : list (Term A n), eqP A eqA n p r -> forall q s : list (Term A n), canonical A0 eqA ltM p -> canonical A0 eqA ltM q -> canonical A0 eqA ltM r -> canonical A0 eqA ltM s -> eqP A eqA n q s -> eqP A eqA n (multpf p q) (multpf r s).
intros p r H'; elim H'; simpl in |- *; auto.
intros ma mb p0 q H'0 H'1 H'2 q0 s H'3 H'4 H'5 H'6 H'7.
cut (canonical A0 eqA ltM p0); [ intros Op0 | apply canonical_imp_canonical with (a := ma); auto ].
cut (canonical A0 eqA ltM q); [ intros Op1 | apply canonical_imp_canonical with (a := mb); auto ].
cut (~ zeroP (A:=A) A0 eqA (n:=n) ma); [ intros Z0 | apply canonical_nzeroP with (ltM := ltM) (p := p0); auto ].
cut (~ zeroP (A:=A) A0 eqA (n:=n) mb); [ intros Z1 | apply canonical_nzeroP with (ltM := ltM) (p := q) ]; auto.
