Require Export Pspoly.
Require Export LetP.
Section Pcomb.
Load hCoefStructure.
Load hOrderStructure.
Load hSpoly.
Inductive CombLinear (Q : list (poly A0 eqA ltM)) : list (Term A n) -> Prop := | CombLinear_0 : CombLinear Q (pO A n) | CombLinear_1 : forall (a : Term A n) (p q s : list (Term A n)), ~ zeroP (A:=A) A0 eqA (n:=n) a -> inPolySet A A0 eqA n ltM q Q -> CombLinear Q p -> eqP A eqA n s (pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec (mults (A:=A) multA (n:=n) a q) p) -> CombLinear Q s.
Hint Resolve CombLinear_0 CombLinear_1 : core.
Hint Resolve CombLinear_canonical : core.
Hint Resolve CombLinear_pluspf : core.
Hint Resolve CombLinear_mults1 : core.
Hint Resolve CombLinear_minuspf : core.
Hint Resolve CombLinear_id : core.
Inductive Grobner (Q : list (poly A0 eqA ltM)) : Prop := Grobner0 : (forall p q : list (Term A n), CombLinear Q p -> reducestar A A0 A1 eqA invA minusA multA divA eqA_dec n ltM ltM_dec Q p q -> eqP A eqA n q (pO A n)) -> Grobner Q.
Inductive ConfluentReduce (Q : list (poly A0 eqA ltM)) : Prop := ConfluentReduce0 : (forall p : list (Term A n), canonical A0 eqA ltM p -> ReduStarConfluent A A0 A1 eqA invA minusA multA divA eqA_dec n ltM ltM_dec Q p) -> ConfluentReduce Q.
Remark CombLinear_trans_cons_lem : forall (a : list (Term A n)) (R : list (poly A0 eqA ltM)), CombLinear R a -> forall (b : poly A0 eqA ltM) (Q : list (poly A0 eqA ltM)), R = b :: Q -> CombLinear Q (s2p A A0 eqA n ltM b) -> CombLinear Q a.
intros a R H'; elim H'; auto.
intros a0 p q s H'0 H'1 H'2 H'3 H'4 b Q H'5 H'6.
apply CombLinear_comp with (p := pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec (mults (A:=A) multA (n:=n) a0 q) p); auto.
2: apply eqp_imp_canonical with (1 := cs) (p := pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec (mults (A:=A) multA (n:=n) a0 q) p); auto.
2: apply (eqp_sym _ _ _ _ _ _ _ _ _ cs n); auto.
2: apply canonical_pluspf; auto.
2: apply canonical_mults with (1 := cs); auto.
2: apply inPolySet_imp_canonical with (L := R); auto.
2: apply CombLinear_canonical with (1 := H'2); auto.
2: apply (eqp_sym _ _ _ _ _ _ _ _ _ cs n); auto.
apply CombLinear_pluspf; auto.
apply CombLinear_mults1; auto.
2: apply H'3 with (b := b); auto.
rewrite H'5 in H'1; inversion H'1; auto.
rewrite <- H2 in H'6; simpl in H'6; auto.
End Pcomb.

Theorem ConfluentReduce_imp_Grobner : forall Q : list (poly A0 eqA ltM), ConfluentReduce Q -> Grobner Q.
intros Q H'; elim H'.
intros H'0.
apply Grobner0; auto.
intros p q H'1; generalize q; clear q; elim H'1.
intros q H'2.
rewrite pO_reducestar with (1 := H'2); auto.
intros a p0 q s H'2 H'3 H'4 H'5 H'6 q0 H'7.
cut (canonical A0 eqA ltM q); [ intros Op0 | apply inPolySet_imp_canonical with (L := Q) ]; auto.
cut (canonical A0 eqA ltM p0); [ intros Op2 | apply CombLinear_canonical with (Q := Q) ]; auto.
cut (canonical A0 eqA ltM s); [ intros Op1 | idtac ].
cut (canonical A0 eqA ltM q0); [ intros Op2b | idtac ]; auto.
cut (reducestar A A0 A1 eqA invA minusA multA divA eqA_dec n ltM ltM_dec Q (mults (A:=A) multA (n:=n) a q) (pO A n)); [ intros H'11 | apply reducestar_in_pO with (1 := cs) ]; auto.
elim red_minus_zero_reduce with (1 := cs) (Q := Q) (p := s) (q := p0) (ltM_dec := ltM_dec) (eqA_dec := eqA_dec); auto.
intros r1 H; elim H; intros H0 H1; clear H.
elim reduce0_reducestar with (ltM_dec := ltM_dec) (eqA_dec := eqA_dec) (1 := cs) (Q := Q) (p := r1); auto.
intros t E'.
lapply (H'0 s); [ intros H'12; inversion H'12 | idtac ]; auto.
apply H; auto.
apply reducestar_eqp_com with (1 := cs) (p := s) (q := t); auto.
apply reducestar_trans with (y := r1) (1 := cs); auto.
apply H'5; auto.
apply (reducestar_trans A A0 A1 eqA plusA invA minusA multA divA cs eqA_dec n ltM ltM_dec os Q) with (y := r1); auto.
apply canonical_reduceplus with (1 := cs) (3 := H1); auto.
apply reduceplus_eqp_com with (1 := cs) (p := mults (A:=A) multA (n:=n) a q) (q := pO A n); auto.
inversion H'11; auto.
apply (eqp_sym _ _ _ _ _ _ _ _ _ cs n); apply (eqp_trans _ _ _ _ _ _ _ _ _ cs n) with (y := minuspf A A0 A1 eqA invA minusA multA eqA_dec n ltM ltM_dec (pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec (mults (A:=A) multA (n:=n) a q) p0) p0); auto.
apply (eqp_trans _ _ _ _ _ _ _ _ _ cs n) with (y := pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec (pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec (mults (A:=A) multA (n:=n) a q) p0) (mults (A:=A) multA (n:=n) (invTerm (A:=A) invA (n:=n) (T1 A1 n)) p0)); auto.
apply (eqp_trans _ _ _ _ _ _ _ _ _ cs n) with (y := pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec (mults (A:=A) multA (n:=n) a q) (pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec p0 (mults (A:=A) multA (n:=n) (invTerm (A:=A) invA (n:=n) (T1 A1 n)) p0))); auto.
apply (eqp_trans _ _ _ _ _ _ _ _ _ cs n) with (y := pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec (mults (A:=A) multA (n:=n) a q) (pO A n)); auto.
inversion H'7.
apply canonical_reduceplus with (1 := cs) (3 := H); auto.
apply eqp_imp_canonical with (1 := cs) (p := pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec (mults (A:=A) multA (n:=n) a q) p0); auto.
apply (eqp_sym _ _ _ _ _ _ _ _ _ cs n); auto.
