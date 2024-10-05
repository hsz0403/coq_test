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

Theorem CombLinear_comp : forall (Q : list (poly A0 eqA ltM)) (p : list (Term A n)), CombLinear Q p -> forall q : list (Term A n), canonical A0 eqA ltM q -> eqP A eqA n p q -> CombLinear Q q.
intros Q p H'; elim H'; auto.
intros q H'0 H'1; inversion H'1; auto.
intros a p0 q s H'0 H'1 H'2 H'3 H'4 q0 H'5 H'6.
cut (canonical A0 eqA ltM q); [ intros C0 | idtac ].
cut (canonical A0 eqA ltM s); [ intros C1 | idtac ].
apply CombLinear_1 with (a := a) (p := p0) (q := q); auto.
apply (eqp_trans _ _ _ _ _ _ _ _ _ cs n) with (y := s); auto; apply (eqp_sym _ _ _ _ _ _ _ _ _ cs n); auto.
apply eqp_imp_canonical with (p := q0) (1 := cs); auto.
apply (eqp_sym _ _ _ _ _ _ _ _ _ cs n); auto.
apply inPolySet_imp_canonical with (L := Q); auto.
