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

Theorem Dmult_is_mulpf : forall (a : Term A n) (nZa : ~ zeroP (A:=A) A0 eqA (n:=n) a) (p q : list (Term A n)), canonical A0 eqA ltM p -> canonical A0 eqA ltM q -> eqP A eqA n (Dmult a nZa (mults (A:=A) multA (n:=n) a p) q) (multpf A A0 eqA plusA multA eqA_dec n ltM ltM_dec p q).
intros a nZa p; elim p; simpl in |- *; auto.
intros a0 l H'0 q H'1 H'2.
cut (canonical A0 eqA ltM l); [ intros Op0 | apply canonical_imp_canonical with (a := a0); auto ].
cut (canonical A0 eqA ltM (multpf A A0 eqA plusA multA eqA_dec n ltM ltM_dec l q)); [ intros Op1 | auto ].
cut (~ zeroP (A:=A) A0 eqA (n:=n) a0); [ intros Z0 | apply canonical_nzeroP with (ltM := ltM) (p := l); auto ].
apply eqp_pluspf_com with (1 := cs); auto.
apply (eqp_trans _ _ _ _ _ _ _ _ _ cs n) with (y := mults (A:=A) multA (n:=n) (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n) (multTerm (A:=A) multA (n:=n) a a0) (b:=a) nZa) q).
apply (eqp_sym _ _ _ _ _ _ _ _ _ cs n).
apply divp_is_multTerm; auto.
apply mults_comp with (1 := cs); auto.
apply (eqTerm_trans _ _ _ _ _ _ _ _ _ cs n) with (y := multTerm (A:=A) multA (n:=n) a0 (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n) a (b:=a) nZa)); auto.
apply (eqTerm_trans _ _ _ _ _ _ _ _ _ cs n) with (y := divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n) (multTerm (A:=A) multA (n:=n) a0 a) (b:=a) nZa); auto.
apply (eqTerm_sym _ _ _ _ _ _ _ _ _ cs n); auto.
