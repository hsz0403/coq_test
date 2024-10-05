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

Theorem reduce_inv2 : forall (Q : list (poly A0 eqA ltM)) (p q : list (Term A n)), reduce Q p q -> canonical A0 eqA ltM p -> exists x : list (Term A n), (exists a : Term A n, ~ zeroP (A:=A) A0 eqA (n:=n) a /\ inPolySet x Q /\ canonical A0 eqA ltM x /\ eqP A eqA n q (minuspf A A0 A1 eqA invA minusA multA eqA_dec n ltM ltM_dec p (mults (A:=A) multA (n:=n) a x))).
intros Q p q H'; elim H'; auto.
intros a b nZb p0 q0 r H'0 H'1 H'2 H'3; cut (canonical A0 eqA ltM (pX b q0)); [ intros C1 | apply inPolySet_imp_canonical with (L := Q); auto ]; exists (pX b q0); exists (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n) a (b:=b) nZb); split; [ idtac | split; [ idtac | split; [ idtac | idtac ] ] ]; auto.
apply (eqp_trans _ _ _ _ _ _ _ _ _ cs n) with (y := spminusf A A0 A1 eqA invA minusA multA divA eqA_dec n ltM ltM_dec a b nZb p0 q0); auto.
apply (eqp_sym _ _ _ _ _ _ _ _ _ cs n); auto.
apply (eqp_trans _ _ _ _ _ _ _ _ _ cs n) with (y := spminusf A A0 A1 eqA invA minusA multA divA eqA_dec n ltM ltM_dec a b nZb (pX a p0) (pX b q0)); auto.
apply spminusf_extend with (1 := cs); auto.
intros a b p0 q0 H'0 H'1 H'2 H'3.
cut (canonical A0 eqA ltM p0); [ intros Op1 | apply canonical_imp_canonical with (a := a) ]; auto.
cut (canonical A0 eqA ltM (pX a q0)); [ intros Op2 | apply canonical_reduce with (Q := Q) (p := pX a p0) ]; auto.
cut (canonical A0 eqA ltM q0); [ intros Op3 | apply canonical_imp_canonical with (a := a) ]; auto.
elim H'1; [ intros x E; elim E; intros a0 E0; elim E0; intros H'4 H'5; elim H'5; intros H'6 H'7; elim H'7; intros H'8 H'9; clear H'7 H'5 E0 E H'1 | clear H'1 ]; auto.
exists x; exists a0; split; [ idtac | split; [ idtac | split ] ]; auto.
apply (eqp_trans _ _ _ _ _ _ _ _ _ cs n) with (y := pX a q0); [ auto | apply (eqp_sym _ _ _ _ _ _ _ _ _ cs n) ].
apply (eqp_sym _ _ _ _ _ _ _ _ _ cs n); auto.
apply (eqp_trans _ _ _ _ _ _ _ _ _ cs n) with (y := pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec (pX a p0) (mults (A:=A) multA (n:=n) (invTerm (A:=A) invA (n:=n) (T1 A1 n)) (mults (A:=A) multA (n:=n) a0 x))); [ auto | idtac ].
cut (~ zeroP (A:=A) A0 eqA (n:=n) a); [ intros Z0 | idtac ].
apply (eqp_trans _ _ _ _ _ _ _ _ _ cs n) with (y := pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec (pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec (pX a (pO A n)) p0) (mults (A:=A) multA (n:=n) (invTerm (A:=A) invA (n:=n) (T1 A1 n)) (mults (A:=A) multA (n:=n) a0 x))).
apply (eqp_sym _ _ _ _ _ _ _ _ _ cs n); apply eqp_pluspf_com with (1 := cs); auto.
apply plusTerm_is_pX with (1 := cs); auto.
apply (eqp_trans _ _ _ _ _ _ _ _ _ cs n) with (y := pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec (pX a (pO A n)) (pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec p0 (mults (A:=A) multA (n:=n) (invTerm (A:=A) invA (n:=n) (T1 A1 n)) (mults (A:=A) multA (n:=n) a0 x)))); [ auto | idtac ].
apply (eqp_trans _ _ _ _ _ _ _ _ _ cs n) with (y := pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec (pX a (pO A n)) (minuspf A A0 A1 eqA invA minusA multA eqA_dec n ltM ltM_dec p0 (mults (A:=A) multA (n:=n) a0 x))).
apply (eqp_sym _ _ _ _ _ _ _ _ _ cs n); auto.
apply (eqp_trans _ _ _ _ _ _ _ _ _ cs n) with (y := pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec (pX a (pO A n)) q0); auto.
apply (eqp_sym _ _ _ _ _ _ _ _ _ cs n); auto.
apply plusTerm_is_pX with (1 := cs); auto.
apply canonical_nzeroP with (ltM := ltM) (p := q0); auto.
