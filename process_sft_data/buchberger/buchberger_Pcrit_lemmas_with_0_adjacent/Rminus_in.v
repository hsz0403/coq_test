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

Theorem Rminus_in : forall (r p q : list (Term A n)) (a b : Term A n) (nZb : ~ zeroP (A:=A) A0 eqA (n:=n) b), divPp b r -> In a p -> canonical A0 eqA ltM p -> canonical A0 eqA ltM (pX b q) -> canonical A0 eqA ltM (pX a r) -> In a (Rminus b nZb p (pX b q) r).
intros r; elim r; simpl in |- *; auto.
intros a l H' p q a0 b nZb H'0 H'1 H'2 H'3 H'4.
cut (~ zeroP (A:=A) A0 eqA (n:=n) b); [ intros Z1 | apply canonical_nzeroP with (ltM := ltM) (p := q); auto ].
elim H'0; intros H'6 H'7; clear H'0.
apply minuspf_in; auto.
apply H'; auto.
apply canonical_skip_fst with (b := a); auto.
apply eqT_compat_ltTl with (b := a); auto.
apply (eqTerm_imp_eqT A eqA n); auto.
inversion H'6; auto.
apply (canonical_pX_order A A0 eqA) with (l := l); auto.
apply canonical_Rminus; auto.
apply canonical_imp_canonical with (a := a); auto.
apply canonical_imp_canonical with (a := a0); auto.
change (canonical A0 eqA ltM (mults (A:=A) multA (n:=n) (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n) a (b:=b) nZb) (pX b q))) in |- *; auto.
