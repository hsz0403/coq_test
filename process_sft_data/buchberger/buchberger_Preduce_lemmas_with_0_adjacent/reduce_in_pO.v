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

Theorem reduce_in_pO : forall (Q : list (poly A0 eqA ltM)) (p : list (Term A n)), inPolySet p Q -> reduce Q p (pO A n).
intros Q p; case p; simpl in |- *; auto.
intros H'; elim (inPolySet_is_pX (pO A n) Q); [ intros a E; elim E; intros q E0; inversion E0 | idtac ]; auto.
intros a l H'.
cut (canonical A0 eqA ltM (pX a l)); [ intros Op0 | idtac ].
cut (canonical A0 eqA ltM l); [ intros Op1 | apply canonical_imp_canonical with (a := a) ]; auto.
cut (~ zeroP (A:=A) A0 eqA (n:=n) a); [ intros Nza | idtac ].
cut (spminusf A A0 A1 eqA invA minusA multA divA eqA_dec n ltM ltM_dec a a Nza l l = pO A n).
intros H'0; rewrite <- H'0.
change (reduce Q (pX a l) (spminusf A A0 A1 eqA invA minusA multA divA eqA_dec n ltM ltM_dec a a Nza l l)) in |- *.
apply reducetop with (b := a) (nZb := Nza) (q := l); auto.
apply divP_on_eqT with (1 := cs); auto.
cut (eqP A eqA n (spminusf A A0 A1 eqA invA minusA multA divA eqA_dec n ltM ltM_dec a a Nza l l) (pO A n)).
intros H'0; inversion H'0; auto.
apply (eqp_trans _ _ _ _ _ _ _ _ _ cs n) with (y := minuspf A A0 A1 eqA invA minusA multA eqA_dec n ltM ltM_dec l (mults (A:=A) multA (n:=n) (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n) a (b:=a) Nza) l)); auto.
apply (eqp_trans _ _ _ _ _ _ _ _ _ cs n) with (y := minuspf A A0 A1 eqA invA minusA multA eqA_dec n ltM ltM_dec l (mults (A:=A) multA (n:=n) (T1 A1 n) l)); auto.
apply (eqp_trans _ _ _ _ _ _ _ _ _ cs n) with (y := minuspf A A0 A1 eqA invA minusA multA eqA_dec n ltM ltM_dec l l); auto.
apply minuspf_refl with (1 := cs); auto.
apply (canonical_nzeroP A A0 eqA n ltM) with (p := l); auto.
apply inPolySet_imp_canonical with (L := Q); auto.
