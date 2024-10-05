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

Theorem ltP_reduce : forall (Q : list (poly A0 eqA ltM)) (p q : list (Term A n)), reduce Q p q -> canonical A0 eqA ltM p -> ltP (A:=A) (n:=n) ltM q p.
intros Q p q H'; elim H'; auto.
2: intros a b p0 q0 H'0 H'1 H'2 H'3; apply ltP_tl; auto.
2: apply (eqT_sym A n); apply (eqTerm_imp_eqT A eqA n); auto.
2: apply H'1; try apply canonical_imp_canonical with (a := a); auto.
intros a b nZb p0; case p0; auto.
intros q0 r H'0 H'1 H'2 H'3.
change (ltP (A:=A) (n:=n) ltM r (pX a (pO A n))) in |- *.
apply (canonical_pX_ltP A A0 eqA); auto.
apply eqp_imp_canonical with (1 := cs) (p := pX a (spminusf A A0 A1 eqA invA minusA multA divA eqA_dec n ltM ltM_dec a b nZb (pO A n) q0)); auto.
apply canonical_spminusf_full_t with (1 := cs); auto.
apply inPolySet_imp_canonical with (L := Q); auto.
intros t l q0 r H'0 H'1 H'2 H'3; apply ltP_trans with (y := pX a (pO A n)); auto.
apply (canonical_pX_ltP A A0 eqA); auto.
apply eqp_imp_canonical with (1 := cs) (p := pX a (spminusf A A0 A1 eqA invA minusA multA divA eqA_dec n ltM ltM_dec a b nZb (pX t l) q0)); auto.
apply canonical_spminusf_full_t with (1 := cs); auto.
apply inPolySet_imp_canonical with (L := Q); auto.
change (ltP (A:=A) (n:=n) ltM (pX a (pO A n)) (pX a (pX t l))) in |- *; auto.
