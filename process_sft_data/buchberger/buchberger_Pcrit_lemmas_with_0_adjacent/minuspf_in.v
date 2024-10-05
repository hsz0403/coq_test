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

Theorem minuspf_in : forall (p q : list (Term A n)) (a b : Term A n), In a p -> ltT ltM b a -> canonical A0 eqA ltM p -> canonical A0 eqA ltM (pX b q) -> In a (minuspf A A0 A1 eqA invA minusA multA eqA_dec n ltM ltM_dec p (pX b q)).
intros p; elim p; simpl in |- *; auto.
intros q a b H'; elim H'; auto.
intros a l H' q a0 b H'0 H'1 H'2 H'3.
elim H'0; [ intros H'4; rewrite H'4; clear H'0 | intros H'4; clear H'0 ].
change (In a0 (minuspf A A0 A1 eqA invA minusA multA eqA_dec n ltM ltM_dec (pX a0 l) (pX b q))) in |- *.
rewrite <- minuspf_inv1_eq; simpl in |- *; auto.
case (ltT_dec A n ltM ltM_dec a b); intros test; [ case test; clear test; intros test | idtac ].
absurd (ltT ltM b a0); auto.
apply ltT_not_ltT; auto.
generalize H'4 H'2; elim l; simpl in |- *; auto.
intros H'0; elim H'0; auto.
intros a1 l0 H'0 H'5; elim H'5; [ intros H'6; rewrite <- H'6; clear H'5 | intros H'6; clear H'5 ]; auto.
intros H'5; apply (ltT_trans A n ltM os) with (y := a); auto.
apply (canonical_pX_order A A0 eqA) with (l := l0); auto.
intros H'5; apply H'0; auto.
change (canonical A0 eqA ltM (pX a l0)) in |- *.
apply canonical_skip_fst with (b := a1); auto.
change (In a0 (minuspf A A0 A1 eqA invA minusA multA eqA_dec n ltM ltM_dec (pX a l) (pX b q))) in |- *.
rewrite <- minuspf_inv1_eq; simpl in |- *; auto.
right; auto.
apply H'; auto.
apply canonical_imp_canonical with (a := a); auto.
absurd (ltT ltM b a0); auto.
apply ltT_not_ltT; auto.
apply eqT_compat_ltTr with (b := a); auto.
generalize H'4 H'2; elim l; simpl in |- *; auto.
intros H'0; elim H'0; auto.
intros a1 l0 H'0 H'5; elim H'5; [ intros H'6; rewrite <- H'6; clear H'5 | intros H'6; clear H'5 ]; auto.
intros H'5; apply (canonical_pX_order A A0 eqA) with (l := l0); auto.
intros H'5; apply H'0; auto.
change (canonical A0 eqA ltM (pX a l0)) in |- *.
apply canonical_skip_fst with (b := a1); auto.
