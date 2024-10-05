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

Theorem Rminus_is_reduceplus : forall (Q : list (poly A0 eqA ltM)) (a : Term A n) (q : list (Term A n)) (nZa : ~ zeroP (A:=A) A0 eqA (n:=n) a), canonical A0 eqA ltM q -> inPolySet A A0 eqA n ltM (pX a q) Q -> forall r : list (Term A n), canonical A0 eqA ltM r -> divPp a r -> forall p : list (Term A n), canonical A0 eqA ltM p -> incl r p -> reduceplus A A0 A1 eqA invA minusA multA divA eqA_dec n ltM ltM_dec Q p (Rminus a nZa p (pX a q) r).
intros Q a q nZa Op0 in0 r; elim r; clear r.
simpl in |- *; intros H' H'0 p H'1 H'2; auto.
apply Rstar_0; auto.
intros a0 r1 Rec Op1 divp0 p Op2 incl0.
cut (canonical A0 eqA ltM r1); [ intros Cr1 | apply canonical_imp_canonical with (a := a0); auto ].
cut (canonical A0 eqA ltM (pX a q)); [ intros Caq | apply inPolySet_imp_canonical with (L := Q); auto ].
elim divp0; intros H' H'0; clear divp0.
apply reduceplus_trans with (1 := cs) (y := Rminus a nZa p (pX a q) r1); auto.
apply Rec; auto.
red in |- *; intros p' H; apply incl0; auto with datatypes.
apply reduceplus_eqp_com with (1 := cs) (p := Rminus a nZa p (pX a q) r1) (q := minuspf A A0 A1 eqA invA minusA multA eqA_dec n ltM ltM_dec (Rminus a nZa p (pX a q) r1) (mults (A:=A) multA (n:=n) (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n) a0 (b:=a) nZa) (pX a q))); auto.
apply reduce_imp_reduceplus with (1 := cs); auto.
apply minus_is_reduce; auto.
apply Rminus_in; auto with datatypes.
