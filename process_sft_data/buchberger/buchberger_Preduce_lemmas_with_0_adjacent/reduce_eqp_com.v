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

Theorem reduce_eqp_com : forall (Q : list (poly A0 eqA ltM)) (p q r s : list (Term A n)), reduce Q p q -> canonical A0 eqA ltM p -> eqP A eqA n p r -> eqP A eqA n q s -> reduce Q r s.
intros Q p q r s H'; generalize r s; clear r s; elim H'; auto.
intros a b nZb p0 q0 r H'0 H'1 H'2 r0 s H'3 H'4 H'5.
inversion_clear H'4.
apply reducetop with (b := b) (nZb := nZb) (q := q0); auto.
apply divP_eqTerm_comp with (1 := cs) (a := a); auto.
apply (eqp_trans _ _ _ _ _ _ _ _ _ cs n) with (y := spminusf A A0 A1 eqA invA minusA multA divA eqA_dec n ltM ltM_dec a b nZb p0 q0); auto.
cut (canonical A0 eqA ltM p0); [ intros Cp0 | apply canonical_imp_canonical with (a := a); auto ].
apply eqp_spminusf_com with (1 := cs); auto.
apply eqp_imp_canonical with (1 := cs) (p := p0); auto.
apply canonical_imp_canonical with (a := b); auto.
apply inPolySet_imp_canonical with (L := Q); auto.
apply (eqp_sym _ _ _ _ _ _ _ _ _ cs n); auto.
apply (eqTerm_sym _ _ _ _ _ _ _ _ _ cs n); auto.
apply divP_eqTerm_comp with (1 := cs) (a := a); auto.
apply (eqp_trans _ _ _ _ _ _ _ _ _ cs n) with (2 := H'5); auto.
intros a b p0 q0 H'0 H'1 H'2 r s H'3 H'4 H'5.
inversion_clear H'4.
inversion_clear H'5.
apply reduceskip; auto.
apply H'1; auto.
apply canonical_imp_canonical with (a := a); auto.
apply (eqTerm_trans _ _ _ _ _ _ _ _ _ cs n) with (y := a); auto.
apply (eqTerm_sym _ _ _ _ _ _ _ _ _ cs n); auto.
apply (eqTerm_trans _ _ _ _ _ _ _ _ _ cs n) with (y := b); auto.
