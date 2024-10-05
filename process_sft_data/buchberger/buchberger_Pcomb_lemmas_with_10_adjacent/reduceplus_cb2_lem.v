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
Admitted.

Theorem reduce_cb : forall (a b : list (Term A n)) (Q : list (poly A0 eqA ltM)), reduce A A0 A1 eqA invA minusA multA divA eqA_dec n ltM ltM_dec Q a b -> canonical A0 eqA ltM a -> CombLinear Q a -> CombLinear Q b.
intros a b Q H' H'0 H'1.
cut (canonical A0 eqA ltM b); [ intros Op1 | apply canonical_reduce with (1 := cs) (3 := H'); auto ].
case reduce_inv2 with (1 := cs) (3 := H'); auto; (intros c E; elim E; intros d E0; elim E0; intros H'7 H'8; elim H'8; intros H'9 H'10; elim H'10; intros H'11 H'12; clear H'10 H'8 E0 E); auto.
apply CombLinear_comp with (p := minuspf A A0 A1 eqA invA minusA multA eqA_dec n ltM ltM_dec a (mults (A:=A) multA (n:=n) d c)); auto.
Admitted.

Theorem reduceplus_cb : forall (a b : list (Term A n)) (Q : list (poly A0 eqA ltM)), reduceplus A A0 A1 eqA invA minusA multA divA eqA_dec n ltM ltM_dec Q a b -> canonical A0 eqA ltM a -> CombLinear Q a -> CombLinear Q b.
intros a b Q H'; elim H'; auto.
intros x y H'0 H'1 H'2.
apply CombLinear_comp with (p := x); auto.
apply eqp_imp_canonical with (p := x) (1 := cs); auto.
intros x y z H'0 H'1 H'2 H'3 H'4.
apply H'2; auto.
apply canonical_reduce with (1 := cs) (3 := H'0) (p := x); auto.
Admitted.

Theorem reducestar_cb : forall (a b : list (Term A n)) (Q : list (poly A0 eqA ltM)), reducestar A A0 A1 eqA invA minusA multA divA eqA_dec n ltM ltM_dec Q a b -> canonical A0 eqA ltM a -> CombLinear Q a -> CombLinear Q b.
intros a b Q H'; elim H'; auto.
intros p q H'0 H'1 H'2 H'3.
Admitted.

Theorem reduce_cb1 : forall (a : poly A0 eqA ltM) (b : list (Term A n)) (Q : list (poly A0 eqA ltM)), reduce A A0 A1 eqA invA minusA multA divA eqA_dec n ltM ltM_dec Q (s2p A A0 eqA n ltM a) b -> CombLinear (a :: Q) b.
intros a; case a; simpl in |- *.
intros x c b Q H'.
cut (canonical A0 eqA ltM b); [ intros Op1 | apply canonical_reduce with (1 := cs) (3 := H') ]; auto.
case reduce_inv2 with (1 := cs) (3 := H'); auto; (intros c1 E; elim E; intros d E0; elim E0; intros H'7 H'8; elim H'8; intros H'9 H'10; elim H'10; intros H'11 H'12; clear H'10 H'8 E0 E).
apply CombLinear_comp with (p := minuspf A A0 A1 eqA invA minusA multA eqA_dec n ltM ltM_dec x (mults (A:=A) multA (n:=n) d c1)); auto.
apply CombLinear_minuspf; auto.
apply CombLinear_id; auto.
generalize c H'; case x; auto.
intros c2 H'0; inversion H'0; auto.
intros t l c0 H'0; change (inPolySet A A0 eqA n ltM (pX t l) (exist (canonical A0 eqA ltM) (pX t l) c0 :: Q)) in |- *; auto.
apply incons with (a := t) (p := l) (P := Q); auto.
apply CombLinear_mults1; auto.
apply CombLinear_id; auto.
apply inskip; auto.
Admitted.

Theorem CombLinear_compo : forall (p : list (Term A n)) (L1 : list (poly A0 eqA ltM)), CombLinear L1 p -> forall L2 : list (poly A0 eqA ltM), (forall q : list (Term A n), inPolySet A A0 eqA n ltM q L1 -> CombLinear L2 q) -> CombLinear L2 p.
intros p L1 H'; elim H'; auto.
intros a p0 q s H'0 H'1 H'2 H'3 H'4 L2 H'5.
apply CombLinear_comp with (p := pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec (mults (A:=A) multA (n:=n) a q) p0); auto.
apply eqp_imp_canonical with (1 := cs) (p := pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec (mults (A:=A) multA (n:=n) a q) p0); auto.
apply (eqp_sym _ _ _ _ _ _ _ _ _ cs n); auto.
apply canonical_pluspf; auto.
apply canonical_mults with (1 := cs); auto.
apply inPolySet_imp_canonical with (L := L1); auto.
apply CombLinear_canonical with (1 := H'2); auto.
Admitted.

Theorem reduceplus_cb1_lem : forall (a b : list (Term A n)) (Q : list (poly A0 eqA ltM)), reduceplus A A0 A1 eqA invA minusA multA divA eqA_dec n ltM ltM_dec Q a b -> forall x : poly A0 eqA ltM, s2p A A0 eqA n ltM x = a -> CombLinear (x :: Q) b.
intros a b Q H'; elim H'; auto.
intros x y H'0 x0; case x0; simpl in |- *; auto.
intros x1 c H'1.
apply CombLinear_comp with (p := x); auto.
rewrite <- H'1; auto.
generalize c; case x1; auto.
intros t l c0; apply CombLinear_id; auto.
change (inPolySet A A0 eqA n ltM (pX t l) (exist (canonical A0 eqA ltM) (pX t l) c0 :: Q)) in |- *; auto.
apply incons with (a := t) (p := l) (P := Q); auto.
apply eqp_imp_canonical with (1 := cs) (p := x1); auto; rewrite H'1; auto.
intros x y z; case y; auto.
intros H'0 H'1 H'2 x0 H'3.
cut (canonical A0 eqA ltM (pO A n)).
intros H'4.
apply CombLinear_compo with (L1 := mks A A0 eqA n ltM (pO A n) H'4 :: Q); auto.
intros q H'5; inversion H'5; auto.
apply CombLinear_id; auto.
apply inskip; auto.
apply canonicalpO; auto.
intros a0 l H'0 H'1 H'2 x0 H'3.
cut (canonical A0 eqA ltM (pX a0 l)).
intros H'4.
apply CombLinear_compo with (L1 := mks A A0 eqA n ltM (pX a0 l) H'4 :: Q); auto.
intros q H'5; inversion H'5; auto.
apply reduce_cb1; auto.
rewrite H'3; auto.
apply CombLinear_id; auto.
apply inskip; auto.
apply canonical_reduce with (1 := cs) (3 := H'0); auto.
generalize H'3; case x0; simpl in |- *; auto.
Admitted.

Theorem reduceplus_cb1 : forall (a : poly A0 eqA ltM) (b : list (Term A n)) (Q : list (poly A0 eqA ltM)), reduceplus A A0 A1 eqA invA minusA multA divA eqA_dec n ltM ltM_dec Q (s2p A A0 eqA n ltM a) b -> CombLinear (a :: Q) b.
intros a b Q H'.
Admitted.

Theorem reducestar_cb1 : forall (a : poly A0 eqA ltM) (b : list (Term A n)) (Q : list (poly A0 eqA ltM)), reducestar A A0 A1 eqA invA minusA multA divA eqA_dec n ltM ltM_dec Q (s2p A A0 eqA n ltM a) b -> CombLinear (a :: Q) b.
intros a b Q H'; inversion H'; auto.
Admitted.

Theorem reduce_cb2 : forall (a b : poly A0 eqA ltM) (Q : list (poly A0 eqA ltM)), reduce A A0 A1 eqA invA minusA multA divA eqA_dec n ltM ltM_dec Q (s2p A A0 eqA n ltM a) (s2p A A0 eqA n ltM b) -> CombLinear (b :: Q) (s2p A A0 eqA n ltM a).
intros a b; case a; case b; simpl in |- *.
intros x c x0 c1 Q H'0.
case reduce_inv2 with (1 := cs) (3 := H'0); auto; intros c0 E; elim E; intros d E0; elim E0; intros H'7 H'8; elim H'8; intros H'9 H'10; elim H'10; intros H'11 H'12; clear H'10 H'8 E0 E.
apply CombLinear_comp with (p := pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec x (mults (A:=A) multA (n:=n) d c0)); auto.
apply CombLinear_pluspf; auto.
generalize c H'0; case x; auto.
intros a0 l c2 H'.
apply CombLinear_id; auto.
change (inPolySet A A0 eqA n ltM (pX a0 l) (exist (canonical A0 eqA ltM) (pX a0 l) c2 :: Q)) in |- *.
apply incons with (a := a0) (p := l) (P := Q); auto.
apply CombLinear_mults1; auto.
apply CombLinear_id; auto.
apply inskip; auto.
apply (eqp_trans _ _ _ _ _ _ _ _ _ cs n) with (y := pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec (minuspf A A0 A1 eqA invA minusA multA eqA_dec n ltM ltM_dec x0 (mults (A:=A) multA (n:=n) d c0)) (mults (A:=A) multA (n:=n) d c0)); auto.
Admitted.

Theorem reduceplus_cb2 : forall (a b : poly A0 eqA ltM) (Q : list (poly A0 eqA ltM)), reduceplus A A0 A1 eqA invA minusA multA divA eqA_dec n ltM ltM_dec Q (s2p A A0 eqA n ltM a) (s2p A A0 eqA n ltM b) -> CombLinear (b :: Q) (s2p A A0 eqA n ltM a).
intros a b Q H'.
apply reduceplus_cb2_lem with (b := s2p A A0 eqA n ltM b); auto.
Admitted.

Theorem reducestar_cb2 : forall (a b : poly A0 eqA ltM) (Q : list (poly A0 eqA ltM)), reducestar A A0 A1 eqA invA minusA multA divA eqA_dec n ltM ltM_dec Q (s2p A A0 eqA n ltM a) (s2p A A0 eqA n ltM b) -> CombLinear (b :: Q) (s2p A A0 eqA n ltM a).
intros a b Q H'; inversion H'; auto.
Admitted.

Theorem reduceplus_cb2_lem : forall (a b : list (Term A n)) (Q : list (poly A0 eqA ltM)), reduceplus A A0 A1 eqA invA minusA multA divA eqA_dec n ltM ltM_dec Q a b -> canonical A0 eqA ltM a -> forall x : poly A0 eqA ltM, s2p A A0 eqA n ltM x = b -> CombLinear (x :: Q) a.
intros a b Q H'; elim H'; auto.
intros x y H'0 H'1 x0 H'2.
apply CombLinear_comp with (p := y); auto.
rewrite <- H'2; case x0; simpl in |- *; auto.
intros x1; case x1; simpl in |- *; auto.
intros t l c; apply CombLinear_id; auto.
change (inPolySet A A0 eqA n ltM (pX t l) (exist (fun l0 => canonical A0 eqA ltM l0) (pX t l) c :: Q)) in |- *; apply incons; auto.
apply (eqp_sym _ _ _ _ _ _ _ _ _ cs n); auto.
intros x y z H'0 H'1 H'2 H'3 x0 H'4.
lapply H'2; [ intros H'5; lapply (H'5 x0); [ intros H'7; clear H'2 | clear H'2 ] | clear H'2 ]; auto.
cut (canonical A0 eqA ltM y).
intros H'2.
lapply (reduce_cb2 (mks A A0 eqA n ltM x H'3) (mks A A0 eqA n ltM y H'2) Q); simpl in |- *; [ intros H'9 | idtac ]; auto.
apply CombLinear_trans_cons_lem with (R := mks A A0 eqA n ltM y H'2 :: x0 :: Q) (b := mks A A0 eqA n ltM y H'2); auto.
apply CombLinear_incl with (P := mks A A0 eqA n ltM y H'2 :: Q); auto.
intros a0 H'6.
apply Incl_inp_inPolySet with (P := mks A A0 eqA n ltM y H'2 :: Q); auto.
red in |- *; simpl in |- *; auto with datatypes.
intros a1 H'8; elim H'8; auto.
apply canonical_reduce with (1 := cs) (3 := H'0); auto.
apply canonical_reduce with (1 := cs) (3 := H'0); auto.
