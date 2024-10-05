Require Export Pspminus.
Section Preduce.
Load hCoefStructure.
Load hOrderStructure.
Load hSpminus.
Inductive inPolySet : list (Term A n) -> list (poly A0 eqA ltM) -> Prop := | incons : forall (a : Term A n) (p : list (Term A n)) (H : canonical A0 eqA ltM (pX a p)) (P : list (poly A0 eqA ltM)), inPolySet (pX a p) (exist (fun l0 : list (Term A n) => canonical A0 eqA ltM l0) (pX a p) H :: P) | inskip : forall (a : poly A0 eqA ltM) (p : list (Term A n)) (P : list (poly A0 eqA ltM)), inPolySet p P -> inPolySet p (a :: P).
Hint Resolve incons inskip : core.
Hint Resolve inPolySet_imp_canonical : core.
Inductive reduce (Q : list (poly A0 eqA ltM)) : list (Term A n) -> list (Term A n) -> Prop := | reducetop : forall (a b : Term A n) (nZb : ~ zeroP (A:=A) A0 eqA (n:=n) b) (p q r : list (Term A n)), inPolySet (pX b q) Q -> divP A A0 eqA multA divA n a b -> eqP A eqA n (spminusf A A0 A1 eqA invA minusA multA divA eqA_dec n ltM ltM_dec a b nZb p q) r -> reduce Q (pX a p) r | reduceskip : forall (a b : Term A n) (p q : list (Term A n)), reduce Q p q -> eqTerm (A:=A) eqA (n:=n) a b -> reduce Q (pX a p) (pX b q).
Hint Resolve reduceskip : core.
Hint Resolve reducetop_sp : core.
Hint Resolve reduce_mults : core.
Definition irreducible (Q : list (poly A0 eqA ltM)) (p : list (Term A n)) := forall q : list (Term A n), ~ reduce Q p q.
Hint Resolve pO_irreducible : core.
Inductive pickinSetp : Term A n -> list (Term A n) -> list (poly A0 eqA ltM) -> Prop := | pickinSeteqp : forall (a b : Term A n) (p : list (Term A n)) (H : canonical A0 eqA ltM (pX b p)) (P : list (poly A0 eqA ltM)), divP A A0 eqA multA divA n a b -> pickinSetp a (pX b p) (exist (fun l0 : list (Term A n) => canonical A0 eqA ltM l0) (pX b p) H :: P) | pickinSetskip : forall (a b : Term A n) (p : list (Term A n)) (q : poly A0 eqA ltM) (P : list (poly A0 eqA ltM)), pickinSetp a p P -> pickinSetp a p (q :: P).
Hint Resolve pickinSeteqp pickinSetskip : core.
Inductive reducehead (Q : list (poly A0 eqA ltM)) : list (Term A n) -> list (Term A n) -> Prop := reduceheadO : forall (a b : Term A n) (nZb : ~ zeroP (A:=A) A0 eqA (n:=n) b) (p q : list (Term A n)), pickinSetp a (pX b q) Q -> reducehead Q (pX a p) (spminusf A A0 A1 eqA invA minusA multA divA eqA_dec n ltM ltM_dec a b nZb p q).
Hint Resolve reduceheadO : core.
Definition s2p : poly A0 eqA ltM -> list (Term A n).
intros H'; elim H'.
intros x H'0; exact x.
Defined.
End Preduce.

Theorem reduce_mults_invf : forall (a : Term A n) (nZa : ~ zeroP (A:=A) A0 eqA (n:=n) a), eqT a (T1 A1 n) -> forall (Q : list (poly A0 eqA ltM)) (p q : list (Term A n)), canonical A0 eqA ltM p -> reduce Q (mults (A:=A) multA (n:=n) a p) q -> reduce Q p (mults (A:=A) multA (n:=n) (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n) (T1 A1 n) (b:=a) nZa) q).
intros a H' eq0 Q p; elim p; auto.
simpl in |- *; intros q H'0 H'1; inversion_clear H'1; auto.
intros a0 l H'0 q H'1 H'2.
cut (canonical A0 eqA ltM l); [ intros Op0 | apply canonical_imp_canonical with (a := a0) ]; auto.
cut (~ zeroP (A:=A) A0 eqA (n:=n) a0); [ intros Z0 | apply canonical_nzeroP with (ltM := ltM) (p := l) ]; auto.
generalize H'0 H'1; inversion_clear H'2; clear H'0 H'1; auto.
intros H'0 H'1.
cut (canonical A0 eqA ltM (pX b q0)); [ intros Op1 | apply inPolySet_imp_canonical with (L := Q) ]; auto.
cut (canonical A0 eqA ltM q0); [ intros Op2 | apply canonical_imp_canonical with (a := b) ]; auto.
cut (divP A A0 eqA multA divA n a0 b); [ intros d0 | idtac ].
apply reduce_eqp_com with (p := pX a0 l) (q := spminusf A A0 A1 eqA invA minusA multA divA eqA_dec n ltM ltM_dec a0 b nZb l q0); auto.
apply mults_eqp_inv with (a := a); auto.
apply (eqp_trans _ _ _ _ _ _ _ _ _ cs n) with (y := mults (A:=A) multA (n:=n) (multTerm (A:=A) multA (n:=n) a (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n) (T1 A1 n) (b:=a) H')) q); auto.
apply (eqp_trans _ _ _ _ _ _ _ _ _ cs n) with (y := mults (A:=A) multA (n:=n) (T1 A1 n) q); auto.
apply (eqp_trans _ _ _ _ _ _ _ _ _ cs n) with (y := q); auto.
apply (eqp_trans _ _ _ _ _ _ _ _ _ cs n) with (y := spminusf A A0 A1 eqA invA minusA multA divA eqA_dec n ltM ltM_dec (multTerm (A:=A) multA (n:=n) a a0) b nZb (mults (A:=A) multA (n:=n) a l) q0); auto.
apply (eqp_sym _ _ _ _ _ _ _ _ _ cs n); auto.
apply spminusf_multTerm with (1 := cs); auto.
apply (eqp_sym _ _ _ _ _ _ _ _ _ cs n); auto.
apply mults_comp with (1 := cs); auto.
apply (eqTerm_trans _ _ _ _ _ _ _ _ _ cs n) with (y := divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n) (multTerm (A:=A) multA (n:=n) a (T1 A1 n)) (b:=a) H'); auto.
apply (eqTerm_trans _ _ _ _ _ _ _ _ _ cs n) with (y := divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n) a (b:=a) H'); auto.
apply (eqTerm_sym _ _ _ _ _ _ _ _ _ cs n); auto.
apply divTerm_multTerm_l with (1 := cs); auto.
apply divTerm_on_eqT with (1 := cs); auto.
apply (eqT_sym A n); auto.
apply eqT_nzero_eqT_divP with (1 := cs) (c := multTerm (A:=A) multA (n:=n) a a0) (nZb := nZb); auto.
apply (eqTerm_imp_eqT A eqA n); auto.
apply (eqT_trans A n) with (y := multTerm (A:=A) multA (n:=n) (T1 A1 n) a0); auto.
apply (eqTerm_imp_eqT A eqA n); auto.
apply (eqT_sym A n); auto.
intros H'0 H'1.
change (reduce Q (pX a0 l) (pX (multTerm (A:=A) multA (n:=n) (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n) (T1 A1 n) (b:=a) H') b) (mults (A:=A) multA (n:=n) (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n) (T1 A1 n) (b:=a) H') q0))) in |- *.
apply reduceskip; auto.
apply (eqTerm_trans _ _ _ _ _ _ _ _ _ cs n) with (y := multTerm (A:=A) multA (n:=n) (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n) (T1 A1 n) (b:=a) H') (multTerm (A:=A) multA (n:=n) a a0)); auto.
apply (eqTerm_trans _ _ _ _ _ _ _ _ _ cs n) with (y := multTerm (A:=A) multA (n:=n) (multTerm (A:=A) multA (n:=n) (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n) (T1 A1 n) (b:=a) H') a) a0); auto.
apply (eqTerm_trans _ _ _ _ _ _ _ _ _ cs n) with (y := multTerm (A:=A) multA (n:=n) (T1 A1 n) a0); auto.
apply eqTerm_multTerm_comp with (1 := cs); auto.
apply divTerm_on_eqT with (1 := cs); auto.
apply (eqT_sym A n); auto.
apply (eqTerm_sym _ _ _ _ _ _ _ _ _ cs n); apply multTerm_assoc with (1 := cs); auto.
