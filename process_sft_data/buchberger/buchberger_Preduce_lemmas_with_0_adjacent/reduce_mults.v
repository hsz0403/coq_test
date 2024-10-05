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

Theorem reduce_mults : forall (Q : list (poly A0 eqA ltM)) (a : Term A n) (p q : list (Term A n)), reduce Q p q -> canonical A0 eqA ltM p -> ~ zeroP (A:=A) A0 eqA (n:=n) a -> reduce Q (mults (A:=A) multA (n:=n) a p) (mults (A:=A) multA (n:=n) a q).
intros Q a p q H'; generalize a; elim H'; clear a H'; auto.
simpl in |- *; auto.
intros a b nZb p0 q0 r H' H'0 H'1 a0 H'2 H'3.
cut (~ zeroP (A:=A) A0 eqA (n:=n) (multTerm (A:=A) multA (n:=n) a0 a)); [ intros nZ0 | idtac ]; auto.
apply reducetop with (b := b) (nZb := nZb) (q := q0); auto.
apply divTerm_def with (nZb := nZb); auto.
apply (eqTerm_trans _ _ _ _ _ _ _ _ _ cs n) with (y := multTerm (A:=A) multA (n:=n) (multTerm (A:=A) multA (n:=n) a0 (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n) a (b:=b) nZb)) b); [ auto | idtac ].
apply (eqTerm_trans _ _ _ _ _ _ _ _ _ cs n) with (y := multTerm (A:=A) multA (n:=n) a0 (multTerm (A:=A) multA (n:=n) (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n) a (b:=b) nZb) b)); [ auto | idtac ].
apply multTerm_assoc with (1 := cs); auto.
apply eqTerm_multTerm_comp with (1 := cs); auto.
apply (eqTerm_sym _ _ _ _ _ _ _ _ _ cs n); apply divTerm_multTerm_l with (1 := cs); auto.
apply (eqp_trans _ _ _ _ _ _ _ _ _ cs n) with (y := mults (A:=A) multA (n:=n) a0 (spminusf A A0 A1 eqA invA minusA multA divA eqA_dec n ltM ltM_dec a b nZb p0 q0)); auto.
apply spminusf_multTerm with (1 := cs); auto.
apply canonical_imp_canonical with (a := a); auto.
apply canonical_imp_canonical with (a := b); auto.
apply inPolySet_imp_canonical with (L := Q); auto.
apply nzeroP_multTerm with (1 := cs); auto.
apply canonical_nzeroP with (ltM := ltM) (p := p0); auto.
intros a b p0 q0 H' H'0 H'1 a0 H'2 H'3.
simpl in |- *; apply reduceskip; auto.
apply H'0; auto.
apply canonical_imp_canonical with (a := a); auto.
