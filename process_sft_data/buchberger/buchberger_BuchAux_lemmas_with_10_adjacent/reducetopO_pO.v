Require Export Pcomb.
Require Export Pcrit.
Require Export Fred.
Require Import moreCoefStructure.
Section BuchAux.
Load hCoefStructure.
Load hOrderStructure.
Load hComb.
Definition red (a : poly A0 eqA ltM) (P : list (poly A0 eqA ltM)) := reducestar A A0 A1 eqA invA minusA multA divA eqA_dec n ltM ltM_dec P (s2p A A0 eqA n ltM a) (pO A n).
Definition addEnd : poly A0 eqA ltM -> list (poly A0 eqA ltM) -> list (poly A0 eqA ltM).
intros a H'0; elim H'0.
exact (a :: nil).
intros b L1 Rec; exact (b :: Rec).
Defined.
Definition spolyp : poly A0 eqA ltM -> poly A0 eqA ltM -> poly A0 eqA ltM.
intros p q; case p; case q.
intros x Cpx x0 Cpx0; exists (spolyf A A0 A1 eqA invA minusA multA divA eqA_dec n ltM ltM_dec x x0 Cpx Cpx0); auto.
apply spolyf_canonical with (1 := cs); auto.
Defined.
Definition spO : poly A0 eqA ltM.
exists (pO A n); simpl in |- *; auto.
Defined.
Definition sp1 : poly A0 eqA ltM.
exists (pX (A1, M1 n) nil); auto.
Defined.
Definition sgen : nat -> poly A0 eqA ltM.
intros m; exists (pX (A1, gen_mon n m) (pO A n)).
apply canonicalp1; auto.
Defined.
Definition sscal : A -> poly A0 eqA ltM -> poly A0 eqA ltM.
intros a p; case p.
intros x H'1; exists (tmults A0 multA eqA_dec (a, M1 n) x); auto.
unfold tmults in |- *; case (zeroP_dec A A0 eqA eqA_dec n (a, M1 n)); simpl in |- *; auto.
Definition zerop : poly A0 eqA ltM -> Prop.
intros H'; case H'.
intros x; case x.
intros H'0; exact True.
intros a l H'0; exact False.
Defined.
Definition divp : poly A0 eqA ltM -> poly A0 eqA ltM -> Prop.
intros H'; case H'.
intros x; case x.
intros H'0 H'1; exact False.
intros a l H'0 H'1; case H'1.
intros x0; case x0.
intros H'2; exact False.
intros a0 l0 H'2.
exact (divP A A0 eqA multA divA n a a0).
Defined.
Definition ppcp : poly A0 eqA ltM -> poly A0 eqA ltM -> poly A0 eqA ltM.
intros H'; case H'.
intros x; case x.
intros H'0 H'1; exists (pO A n); auto.
intros a l H'0 H'1; case H'1.
intros x0; case x0.
intros H'2; exists (pO A n); auto.
intros a0 l0 H'2; exists (ppc (A:=A) A1 (n:=n) a a0 :: pO A n).
change (canonical A0 eqA ltM (pX (ppc (A:=A) A1 (n:=n) a a0) (pO A n))) in |- *; apply canonicalp1; auto.
apply ppc_nZ with (1 := cs); auto.
apply canonical_nzeroP with (ltM := ltM) (p := l); auto.
apply canonical_nzeroP with (ltM := ltM) (p := l0); auto.
Defined.
Hint Resolve pO_irreducible : core.
Hint Resolve reducetopO_pO : core.
Definition Cb : poly A0 eqA ltM -> list (poly A0 eqA ltM) -> Prop.
intros H'; case H'.
intros x H'0 Q; exact (CombLinear A A0 eqA plusA multA eqA_dec n ltM ltM_dec Q x).
Defined.
Remark CombLinear_trans1 : forall (a : list (Term A n)) (R : list (poly A0 eqA ltM)), CombLinear A A0 eqA plusA multA eqA_dec n ltM ltM_dec R a -> forall (b : poly A0 eqA ltM) (Q : list (poly A0 eqA ltM)), R = addEnd b Q -> CombLinear A A0 eqA plusA multA eqA_dec n ltM ltM_dec Q (s2p A A0 eqA n ltM b) -> CombLinear A A0 eqA plusA multA eqA_dec n ltM ltM_dec Q a.
intros a R H'; elim H'; auto.
intros b Q H'0 H'1.
apply CombLinear_0; auto.
intros a0 p q s H'0 H'1 H'2 H'3 H'4 b Q H'5 H'6.
apply CombLinear_comp with (1 := cs) (p := pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec (mults (A:=A) multA (n:=n) a0 q) p); auto.
2: apply eqp_imp_canonical with (1 := cs) (p := pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec (mults (A:=A) multA (n:=n) a0 q) p); auto.
2: apply (eqp_sym _ _ _ _ _ _ _ _ _ cs n); auto.
2: apply canonical_pluspf with (1 := os); auto.
2: apply canonical_mults with (1 := cs); auto.
2: apply inPolySet_imp_canonical with (L := R); auto.
2: apply CombLinear_canonical with (eqA_dec := eqA_dec) (ltM_dec := ltM_dec) (1 := cs) (Q := R); auto.
2: apply (eqp_sym _ _ _ _ _ _ _ _ _ cs n); auto.
apply CombLinear_pluspf with (1 := cs); auto.
apply CombLinear_mults1 with (1 := cs); auto.
2: apply H'3 with (b := b); auto.
case (inPolySet_addEnd q b Q); auto.
rewrite <- H'5; auto.
intros H'7; rewrite H'7; auto.
intros; (apply CombLinear_id with (1 := cs); auto).
Definition unit : poly A0 eqA ltM -> Term A n.
intros p; case p.
intros x; case x.
intros H'; exact (T1 A1 n).
intros a l; case a.
intros co m H'; cut (~ eqA co A0).
intros H'0; exact (divA A1 co H'0, M1 n).
inversion H'; auto.
simpl in H0.
intuition.
Defined.
Hint Resolve divA_nZ : core.
Definition nf : poly A0 eqA ltM -> list (poly A0 eqA ltM) -> poly A0 eqA ltM.
intros p L.
case (Reducef A A0 A1 eqA plusA invA minusA multA divA cs eqA_dec n ltM ltM_dec os L p).
intros x H'.
apply LetP with (A := poly A0 eqA ltM) (h := x).
intros u H'1; case u.
intros x0 H'2; exists (mults (A:=A) multA (n:=n) (unit (mks A A0 eqA n ltM x0 H'2)) x0); auto.
apply canonical_mults with (1 := cs); auto.
apply unit_nZ; auto.
Defined.
Hint Resolve canonical_s2p : core.
Definition foreigner : poly A0 eqA ltM -> poly A0 eqA ltM -> Prop.
intros a b; case a; case b.
intros x; case x.
intros H' x0 H'0; exact True.
intros a0 l H' x0; case x0.
intros H'0; exact True.
intros a1 l0 H'0; exact (eqT (ppc (A:=A) A1 (n:=n) a0 a1) (multTerm (A:=A) multA (n:=n) a0 a1)).
Defined.
Definition foreigner_dec : forall a b : poly A0 eqA ltM, {foreigner a b} + {~ foreigner a b}.
intros a b; case a; case b.
intros x; case x.
simpl in |- *; auto.
intros a0 l c x0; case x0; simpl in |- *; auto.
intros a1 l0 H'.
apply eqT_dec; auto.
Defined.
End BuchAux.

Definition zerop : poly A0 eqA ltM -> Prop.
intros H'; case H'.
intros x; case x.
intros H'0; exact True.
Admitted.

Theorem zerop_dec : forall a : poly A0 eqA ltM, {zerop a} + {~ zerop a}.
intros H'; case H'.
intros x; case x.
intros c; left; simpl in |- *; auto.
Admitted.

Definition divp : poly A0 eqA ltM -> poly A0 eqA ltM -> Prop.
intros H'; case H'.
intros x; case x.
intros H'0 H'1; exact False.
intros a l H'0 H'1; case H'1.
intros x0; case x0.
intros H'2; exact False.
intros a0 l0 H'2.
Admitted.

Theorem divp_trans : transitive (poly A0 eqA ltM) divp.
red in |- *.
intros x y z; case x; case y; case z.
intros x0 c x1 c0 x2 c1; generalize c c0 c1; case x0; case x1; case x2; simpl in |- *; auto.
intros a l a0 l0 H' H'0 H'1 H'2; elim H'2.
intros a l a0 l0 a1 l1 H' H'0 H'1 H'2 H'3.
Admitted.

Theorem divp_dec : forall a b : poly A0 eqA ltM, {divp a b} + {~ divp a b}.
intros a b; case a; case b.
intros x c x0 c0; generalize c c0; case x; case x0; simpl in |- *.
intros H' H'0; right; red in |- *; intros H'1; elim H'1.
intros a0 l H' H'0; right; red in |- *; intros H'1; elim H'1.
intros a0 l H' H'0; right; red in |- *; intros H'1; elim H'1.
intros a0 l a1 l0 H' H'0.
apply divP_dec with (1 := cs); auto.
apply canonical_nzeroP with (ltM := ltM) (p := l); auto.
Admitted.

Definition ppcp : poly A0 eqA ltM -> poly A0 eqA ltM -> poly A0 eqA ltM.
intros H'; case H'.
intros x; case x.
intros H'0 H'1; exists (pO A n); auto.
intros a l H'0 H'1; case H'1.
intros x0; case x0.
intros H'2; exists (pO A n); auto.
intros a0 l0 H'2; exists (ppc (A:=A) A1 (n:=n) a a0 :: pO A n).
change (canonical A0 eqA ltM (pX (ppc (A:=A) A1 (n:=n) a a0) (pO A n))) in |- *; apply canonicalp1; auto.
apply ppc_nZ with (1 := cs); auto.
apply canonical_nzeroP with (ltM := ltM) (p := l); auto.
Admitted.

Theorem divp_ppc : forall a b c : poly A0 eqA ltM, divp (ppcp a b) c -> divp (ppcp b a) c.
intros a b c; (case a; case b; case c).
intros x c0 x0 c1 x1 c2; generalize c0 c1 c2; case x; case x0; case x1; simpl in |- *; auto.
intros a0 l a1 l0 a2 l1 H' H'0 H'1 H'2.
Admitted.

Theorem zerop_ddivp_ppc : forall a b : poly A0 eqA ltM, ~ zerop a -> ~ zerop b -> divp (ppcp a b) b.
intros a b; (case a; case b).
intros x c0 x0 c1; generalize c0 c1; case x; case x0; simpl in |- *; auto.
intros a0 l a1 l0 H' H'0 H'1 H'2.
apply divP_ppcr with (1 := cs); auto.
apply canonical_nzeroP with (ltM := ltM) (p := l); auto.
Admitted.

Theorem divp_nzeropl : forall a b : poly A0 eqA ltM, divp a b -> ~ zerop a.
intros a b; (case a; case b).
Admitted.

Theorem divp_nzeropr : forall a b : poly A0 eqA ltM, divp a b -> ~ zerop b.
intros a b; (case a; case b).
Admitted.

Theorem zerop_red_spoly_l : forall a b : poly A0 eqA ltM, zerop a -> forall Q : list (poly A0 eqA ltM), red (spolyp a b) Q.
intros a b; (case a; case b).
intros x c0 x0 c1; generalize c0 c1; case x; case x0; simpl in |- *; auto.
intros c2 c3 H' Q; unfold red in |- *; simpl in |- *; auto.
intros a0 l c2 c3 H'; elim H'.
intros a0 l c2 c3 H' Q; unfold red in |- *; simpl in |- *; auto.
Admitted.

Theorem zerop_red_spoly_r : forall a b : poly A0 eqA ltM, zerop b -> forall Q : list (poly A0 eqA ltM), red (spolyp a b) Q.
intros a b; (case a; case b).
intros x c0 x0 c1; generalize c0 c1; case x; case x0; simpl in |- *; auto.
intros c2 c3 H' Q; unfold red in |- *; simpl in |- *; auto.
intros a0 l c2 c3 H' Q; unfold red in |- *; simpl in |- *; auto.
intros a0 l c2 c3 H'; elim H'.
Admitted.

Theorem divP_ppc : forall a b c : poly A0 eqA ltM, divp a b -> divp a c -> divp a (ppcp b c).
intros a b c; (case a; case b; case c).
intros x c0 x0 c1 x1 c2; generalize c0 c1 c2; case x; case x0; case x1; simpl in |- *; auto.
intros a0 l a1 l0 a2 l1 H' H'0 H'1 H'2 H'3.
elim ppc_is_ppcm with (1 := cs) (a := a1) (b := a2); auto.
apply canonical_nzeroP with (ltM := ltM) (p := l0); auto.
Admitted.

Definition Cb : poly A0 eqA ltM -> list (poly A0 eqA ltM) -> Prop.
intros H'; case H'.
Admitted.

Theorem Cb_id : forall (a : poly A0 eqA ltM) (Q : list (poly A0 eqA ltM)), In a Q -> Cb a Q.
intros a; case a; simpl in |- *.
intros x; case x; auto.
intros c Q H'.
replace (nil (A:=Term A n)) with (pO A n); auto; apply CombLinear_0; auto.
intros a0 l c Q H'.
apply CombLinear_id with (1 := cs); auto.
change (inPolySet A A0 eqA n ltM (s2p A A0 eqA n ltM (mks A A0 eqA n ltM (pX a0 l) c)) Q) in |- *; apply in_inPolySet; auto.
Admitted.

Theorem inPolySet_addEnd : forall (a : list (Term A n)) (p : poly A0 eqA ltM) (l : list (poly A0 eqA ltM)), inPolySet A A0 eqA n ltM a (addEnd p l) -> a = s2p A A0 eqA n ltM p \/ inPolySet A A0 eqA n ltM a l.
intros a p l; elim l; simpl in |- *; auto.
intros H'; inversion H'; auto.
intros a0 l0 H' H'0; inversion H'0; auto.
right.
exact (incons A A0 eqA n ltM a1 p0 H l0).
case H'; auto.
intros H3; right; try assumption.
Admitted.

Remark CombLinear_trans1 : forall (a : list (Term A n)) (R : list (poly A0 eqA ltM)), CombLinear A A0 eqA plusA multA eqA_dec n ltM ltM_dec R a -> forall (b : poly A0 eqA ltM) (Q : list (poly A0 eqA ltM)), R = addEnd b Q -> CombLinear A A0 eqA plusA multA eqA_dec n ltM ltM_dec Q (s2p A A0 eqA n ltM b) -> CombLinear A A0 eqA plusA multA eqA_dec n ltM ltM_dec Q a.
intros a R H'; elim H'; auto.
intros b Q H'0 H'1.
apply CombLinear_0; auto.
intros a0 p q s H'0 H'1 H'2 H'3 H'4 b Q H'5 H'6.
apply CombLinear_comp with (1 := cs) (p := pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec (mults (A:=A) multA (n:=n) a0 q) p); auto.
2: apply eqp_imp_canonical with (1 := cs) (p := pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec (mults (A:=A) multA (n:=n) a0 q) p); auto.
2: apply (eqp_sym _ _ _ _ _ _ _ _ _ cs n); auto.
2: apply canonical_pluspf with (1 := os); auto.
2: apply canonical_mults with (1 := cs); auto.
2: apply inPolySet_imp_canonical with (L := R); auto.
2: apply CombLinear_canonical with (eqA_dec := eqA_dec) (ltM_dec := ltM_dec) (1 := cs) (Q := R); auto.
2: apply (eqp_sym _ _ _ _ _ _ _ _ _ cs n); auto.
apply CombLinear_pluspf with (1 := cs); auto.
apply CombLinear_mults1 with (1 := cs); auto.
2: apply H'3 with (b := b); auto.
case (inPolySet_addEnd q b Q); auto.
rewrite <- H'5; auto.
intros H'7; rewrite H'7; auto.
Admitted.

Theorem Cb_trans : forall (a b : poly A0 eqA ltM) (Q : list (poly A0 eqA ltM)), Cb a (addEnd b Q) -> Cb b Q -> Cb a Q.
intros a b; case a; case b; simpl in |- *; auto.
intros x c x0 H' Q H'0 H'1.
Admitted.

Theorem Cb_incl : forall (a : poly A0 eqA ltM) (P Q : list (poly A0 eqA ltM)), (forall a : poly A0 eqA ltM, In a P -> In a Q) -> Cb a P -> Cb a Q.
intros a; case a; simpl in |- *; auto.
intros x H' P Q H'0 H'1.
apply CombLinear_incl with (1 := cs) (P := P); auto.
intros a0 H'2.
Admitted.

Theorem Cb_in1 : forall (a b : poly A0 eqA ltM) (Q : list (poly A0 eqA ltM)), Cb a Q -> Cb a (b :: Q).
intros a b Q H'.
Admitted.

Theorem reducetopO_pO : forall Q : list (poly A0 eqA ltM), reducestar A A0 A1 eqA invA minusA multA divA eqA_dec n ltM ltM_dec Q (pO A n) (pO A n).
intros Q; apply reducestar0; auto.
apply Rstar_0; auto.
