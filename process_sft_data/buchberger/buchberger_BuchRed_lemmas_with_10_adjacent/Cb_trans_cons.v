Require Export Pcomb.
Require Export Pcrit.
Require Export Buch.
Require Export Fred.
Require Import Buch.
Section BuchRed.
Load hCoefStructure.
Load hOrderStructure.
Load hBuch.
Definition reducep (L : list (poly A0 eqA ltM)) (p q : poly A0 eqA ltM) : Prop := reduce A A0 A1 eqA invA minusA multA divA eqA_dec n ltM ltM_dec L (s2p A A0 eqA n ltM p) (s2p A A0 eqA n ltM q).
Hint Resolve zerop_nf_cb : core.
Definition redacc : list (poly A0 eqA ltM) -> list (poly A0 eqA ltM) -> list (poly A0 eqA ltM).
intros H'; elim H'.
intros L; exact (nil (A:=poly A0 eqA ltM)).
intros a p Rec Acc.
apply LetP with (A := poly A0 eqA ltM) (h := nf A A0 A1 eqA plusA invA minusA multA divA cs eqA_dec n ltM ltM_dec os a (p ++ Acc)).
intros u H'0; case (zerop_dec A A0 eqA n ltM u); intros Z.
exact (Rec Acc).
exact (u :: Rec (u :: Acc)).
Defined.
Definition Red (L : list (poly A0 eqA ltM)) : list (poly A0 eqA ltM) := redacc L nil.
Definition redbuch (L : list (poly A0 eqA ltM)) : list (poly A0 eqA ltM) := Red (buch A A0 A1 eqA plusA invA minusA multA divA cs eqA_dec n ltM ltM_dec os L).
End BuchRed.

Theorem Cb_addEnd_cons : forall (L : list (poly A0 eqA ltM)) (p q : poly A0 eqA ltM), Cb A A0 eqA plusA multA eqA_dec n ltM ltM_dec q (addEnd A A0 eqA n ltM p L) -> Cb A A0 eqA plusA multA eqA_dec n ltM ltM_dec q (p :: L).
intros L p q H; apply Cb_incl with (1 := cs) (P := addEnd A A0 eqA n ltM p L); auto.
elim L; simpl in |- *; auto.
intros a l H0 a0 H1; elim H1; clear H1; intros H1; auto.
Admitted.

Theorem Cb_cons_addEnd : forall (L : list (poly A0 eqA ltM)) (p q : poly A0 eqA ltM), Cb A A0 eqA plusA multA eqA_dec n ltM ltM_dec q (p :: L) -> Cb A A0 eqA plusA multA eqA_dec n ltM ltM_dec q (addEnd A A0 eqA n ltM p L).
intros L p q H; apply Cb_incl with (1 := cs) (P := p :: L); auto.
elim L; simpl in |- *; auto.
intros a l H0 a0 H1; elim H1; clear H1; intros H1; auto.
Admitted.

Theorem Cb_cons : forall (p : poly A0 eqA ltM) (L : list (poly A0 eqA ltM)), Cb A A0 eqA plusA multA eqA_dec n ltM ltM_dec (nf A A0 A1 eqA plusA invA minusA multA divA cs eqA_dec n ltM ltM_dec os p L) (p :: L).
intros p L; unfold nf, LetP in |- *; auto.
case (Reducef A A0 A1 eqA plusA invA minusA multA divA cs eqA_dec n ltM ltM_dec os L p); simpl in |- *; auto.
intros x0; case x0; simpl in |- *.
intros x c H'.
change (CombLinear A A0 eqA plusA multA eqA_dec n ltM ltM_dec (p :: L) (mults (A:=A) multA (n:=n) (unit A A0 A1 eqA divA n ltM (mks A A0 eqA n ltM x c)) x)) in |- *.
apply CombLinear_mults1 with (1 := cs); auto.
apply unit_nZ with (1 := cs); auto.
Admitted.

Theorem Cb_comp : forall L1 L2 : list (poly A0 eqA ltM), (forall p : poly A0 eqA ltM, In p L1 -> Cb A A0 eqA plusA multA eqA_dec n ltM ltM_dec p L2) -> forall q : poly A0 eqA ltM, Cb A A0 eqA plusA multA eqA_dec n ltM ltM_dec q L1 -> Cb A A0 eqA plusA multA eqA_dec n ltM ltM_dec q L2.
intros L1 L2 H' q; case q; simpl in |- *.
intros x H'0 H'1.
apply CombLinear_compo with (1 := cs) (L1 := L1); auto.
intros q0 H'2.
case inPolySet_inv1 with (1 := H'2); auto.
intros q1 H; elim H; intros H0 H1; clear H.
lapply (H' q1); [ intros H'6 | idtac ]; auto.
generalize H'6 H1; case q1; simpl in |- *; auto.
Admitted.

Theorem Cb_nf : forall (p : poly A0 eqA ltM) (L : list (poly A0 eqA ltM)), Cb A A0 eqA plusA multA eqA_dec n ltM ltM_dec p (nf A A0 A1 eqA plusA invA minusA multA divA cs eqA_dec n ltM ltM_dec os p L :: L).
intros p L; unfold nf in |- *.
case (Reducef A A0 A1 eqA plusA invA minusA multA divA cs eqA_dec n ltM ltM_dec os L p); auto.
case p.
unfold LetP in |- *; intros x H' x0; case x0; simpl in |- *.
intros x1 c H'0.
change (CombLinear A A0 eqA plusA multA eqA_dec n ltM ltM_dec (mks A A0 eqA n ltM (mults (A:=A) multA (n:=n) (unit A A0 A1 eqA divA n ltM (mks A A0 eqA n ltM x1 c)) x1) (canonical_mults A A0 A1 eqA plusA invA minusA multA divA cs eqA_dec n ltM os (unit A A0 A1 eqA divA n ltM (mks A A0 eqA n ltM x1 c)) x1 (unit_nZ A A0 A1 eqA plusA invA minusA multA divA cs n ltM (mks A A0 eqA n ltM x1 c)) c) :: L) x) in |- *.
apply CombLinear_compo with (1 := cs) (L1 := mks A A0 eqA n ltM x1 c :: L); auto.
change (CombLinear A A0 eqA plusA multA eqA_dec n ltM ltM_dec (mks A A0 eqA n ltM x1 c :: L) (s2p A A0 eqA n ltM (mks A A0 eqA n ltM x H'))) in |- *.
apply reducestar_cb2 with (1 := cs); auto.
intros q H'1; inversion H'1; auto.
2: apply CombLinear_id with (1 := cs); auto.
2: apply inskip; auto.
generalize c H2; case x1; auto.
intros c0 H'2; inversion H'2.
intros a0 l c0 H'2.
cut (~ zeroP (A:=A) A0 eqA (n:=n) (unit A A0 A1 eqA divA n ltM (mks A A0 eqA n ltM (a0 :: l) c0))); [ intros nZu | idtac ]; auto.
apply CombLinear_1 with (a := divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n) (T1 A1 n) (b:=unit A A0 A1 eqA divA n ltM (mks A A0 eqA n ltM (pX a0 l) c0)) nZu) (p := pO A n) (q := mults (A:=A) multA (n:=n) (unit A A0 A1 eqA divA n ltM (mks A A0 eqA n ltM (pX a0 l) c0)) (pX a0 l)); auto.
simpl in |- *; auto.
change (inPolySet A A0 eqA n ltM (pX (multTerm (A:=A) multA (n:=n) (unit A A0 A1 eqA divA n ltM (mks A A0 eqA n ltM (pX a0 l) c0)) a0) (mults (A:=A) multA (n:=n) (unit A A0 A1 eqA divA n ltM (mks A A0 eqA n ltM (pX a0 l) c0)) l)) (exist (fun a1 => canonical A0 eqA ltM a1) (pX (multTerm (A:=A) multA (n:=n) (unit A A0 A1 eqA divA n ltM (mks A A0 eqA n ltM (a0 :: l) c0)) a0) (mults (A:=A) multA (n:=n) (unit A A0 A1 eqA divA n ltM (mks A A0 eqA n ltM (a0 :: l) c0)) l)) (canonical_mults A A0 A1 eqA plusA invA minusA multA divA cs eqA_dec n ltM os (unit A A0 A1 eqA divA n ltM (mks A A0 eqA n ltM (pX a0 l) c0)) (pX a0 l) (unit_nZ _ _ _ _ _ _ _ _ _ cs _ ltM (mks A A0 eqA n ltM (pX a0 l) c0)) c0) :: L)) in |- *.
apply incons; auto.
apply CombLinear_0; auto.
apply (eqp_trans _ _ _ _ _ _ _ _ _ cs n) with (y := mults (A:=A) multA (n:=n) (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n) (T1 A1 n) (b:=unit A A0 A1 eqA divA n ltM (mks A A0 eqA n ltM (a0 :: l) c0)) nZu) (mults (A:=A) multA (n:=n) (unit A A0 A1 eqA divA n ltM (mks A A0 eqA n ltM (a0 :: l) c0)) (a0 :: l))); auto.
2: apply (eqp_sym _ _ _ _ _ _ _ _ _ cs n); auto.
apply (eqp_trans _ _ _ _ _ _ _ _ _ cs n) with (y := mults (A:=A) multA (n:=n) (multTerm (A:=A) multA (n:=n) (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n) (T1 A1 n) (b:=unit A A0 A1 eqA divA n ltM (mks A A0 eqA n ltM (a0 :: l) c0)) nZu) (unit A A0 A1 eqA divA n ltM (mks A A0 eqA n ltM (a0 :: l) c0))) (a0 :: l)); auto.
apply (eqp_trans _ _ _ _ _ _ _ _ _ cs n) with (y := mults (A:=A) multA (n:=n) (T1 A1 n) (a0 :: l)); auto.
rewrite H'2; auto.
apply (eqp_sym _ _ _ _ _ _ _ _ _ cs n); auto.
apply mults_comp with (1 := cs); auto.
apply divTerm_on_eqT with (1 := cs); auto.
apply (eqT_sym A n); auto.
apply unit_T1; auto.
Admitted.

Theorem zerop_elim_Cb : forall (L : list (poly A0 eqA ltM)) (p q : poly A0 eqA ltM), zerop A A0 eqA n ltM p -> Cb A A0 eqA plusA multA eqA_dec n ltM ltM_dec q (p :: L) -> Cb A A0 eqA plusA multA eqA_dec n ltM ltM_dec q L.
intros L p q H' H'0.
apply Cb_comp with (L1 := p :: L); auto.
simpl in |- *; auto.
intros p0 H'1; case H'1; [ intros H'2; rewrite <- H'2; clear H'1 | intros H'2; clear H'1 ]; auto.
generalize H'; case p; simpl in |- *; auto.
intros x; case x; simpl in |- *; auto.
intros H'1 H'3; try assumption.
change (CombLinear A A0 eqA plusA multA eqA_dec n ltM ltM_dec L (pO A n)) in |- *.
apply CombLinear_0; auto.
intros a l H'1 H'3; elim H'3; auto.
Admitted.

Theorem Cb_compo : forall (p : poly A0 eqA ltM) (L1 : list (poly A0 eqA ltM)), Cb A A0 eqA plusA multA eqA_dec n ltM ltM_dec p L1 -> forall L2 : list (poly A0 eqA ltM), (forall q : poly A0 eqA ltM, In q L1 -> Cb A A0 eqA plusA multA eqA_dec n ltM ltM_dec q L2) -> Cb A A0 eqA plusA multA eqA_dec n ltM ltM_dec p L2.
intros p L1 H' L2 H'0.
Admitted.

Theorem grobner_def : forall L : list (poly A0 eqA ltM), Grobner A A0 A1 eqA plusA invA minusA multA divA eqA_dec n ltM ltM_dec L -> forall p : poly A0 eqA ltM, Cb A A0 eqA plusA multA eqA_dec n ltM ltM_dec p L -> zerop A A0 eqA n ltM p \/ (exists q : poly A0 eqA ltM, reducep L p q).
intros L H'; inversion H'; auto.
intros p H'0.
case (Reducef A A0 A1 eqA plusA invA minusA multA divA cs eqA_dec n ltM ltM_dec os L p).
intros x H'1; inversion H'.
lapply (H0 (s2p A A0 eqA n ltM p) (s2p A A0 eqA n ltM x)); [ intros H'4; lapply H'4; [ clear H'4 | clear H'4 ] | idtac ]; auto.
inversion H'1; auto.
inversion H1; auto.
intros H'2; left.
cut (eqP A eqA n (s2p A A0 eqA n ltM p) (pO A n)); auto.
case p; simpl in |- *; auto.
intros x1; case x1; auto.
intros a l H'3 H'4; inversion H'4.
apply (eqp_trans _ _ _ _ _ _ _ _ _ cs n) with (y := s2p A A0 eqA n ltM x); auto.
intros H'2; right; cut (canonical A0 eqA ltM y); auto.
intros H'3; exists (mks A A0 eqA n ltM y H'3); generalize H5; case p; simpl in |- *; auto.
apply canonical_reduce with (1 := cs) (3 := H5); auto.
generalize H'0; case p; simpl in |- *; auto.
Admitted.

Theorem def_grobner : forall L : list (poly A0 eqA ltM), (forall p : poly A0 eqA ltM, Cb A A0 eqA plusA multA eqA_dec n ltM ltM_dec p L -> zerop A A0 eqA n ltM p \/ (exists q : poly A0 eqA ltM, reducep L p q)) -> Grobner A A0 A1 eqA plusA invA minusA multA divA eqA_dec n ltM ltM_dec L.
intros L H'.
apply Grobner0.
intros p q H'0 H'1.
cut (canonical A0 eqA ltM p).
intros H'2.
cut (canonical A0 eqA ltM q).
intros H'3.
elim (H' (mks A A0 eqA n ltM q H'3)); [ intros H'6 | intros H'6 | idtac ]; auto.
generalize H'3 H'6; case q; simpl in |- *; auto.
intros a l H'4 H'5; elim H'5; auto.
case H'6; intros q0 E; clear H'6.
inversion H'1.
generalize H0 E; case q0; auto.
simpl in |- *; auto.
intros x H'4 H'5 H'6; absurd (reduce A A0 A1 eqA invA minusA multA divA eqA_dec n ltM ltM_dec L q x); auto.
simpl in |- *; auto.
apply reducestar_cb with (a := p) (1 := cs); auto.
inversion H'1.
apply canonical_reduceplus with (1 := cs) (3 := H); auto.
Admitted.

Theorem reduce_divp : forall (p q : poly A0 eqA ltM) (Q : list (poly A0 eqA ltM)), reduce A A0 A1 eqA invA minusA multA divA eqA_dec n ltM ltM_dec Q (s2p A A0 eqA n ltM p) (s2p A A0 eqA n ltM q) -> exists r : poly A0 eqA ltM, In r (q :: Q) /\ divp A A0 eqA multA divA n ltM p r /\ ~ zerop A A0 eqA n ltM r.
intros p q; case p; case q; simpl in |- *.
intros x H' x0 c Q H'0; inversion H'0.
generalize c; rewrite <- H2; simpl in |- *; auto.
case inPolySet_inv1 with (1 := H); auto.
intros q1 E; case E; intros H'1 H'2; clear E.
intros c0; exists q1; split; [ right | split ]; auto.
generalize H'2; case q1; simpl in |- *; auto.
intros x1; case x1; auto.
intros H'4 H'5; discriminate H'5; auto.
intros a0 l H'4 H'5; injection H'5; intros.
rewrite <- H5; trivial.
generalize H'1 H'2 c0; case q1; simpl in |- *; auto.
intros x1; case x1; auto.
intros c1 H'3 H'4; discriminate H'4.
exists (exist (fun l : list (Term A n) => canonical A0 eqA ltM l) x H'); split; [ left | split ]; simpl in |- *; auto.
generalize c; rewrite <- H1; unfold pX in |- *; auto.
generalize H'; rewrite <- H2; unfold pX in |- *; auto.
intros H'1 H'2.
apply divP_eqTerm_comp with (a := b) (1 := cs); auto.
cut (~ zeroP (A:=A) A0 eqA (n:=n) b); [ intros Z | idtac ]; auto.
apply divTerm_def with (nZb := Z); auto.
apply canonical_nzeroP with (ltM := ltM) (p := q0); auto.
apply (eqTerm_sym _ _ _ _ _ _ _ _ _ cs n); auto.
Admitted.

Theorem reduceplus_divp_lem : forall (a b : list (Term A n)) (Q : list (poly A0 eqA ltM)), reduceplus A A0 A1 eqA invA minusA multA divA eqA_dec n ltM ltM_dec Q a b -> canonical A0 eqA ltM a -> forall x y : poly A0 eqA ltM, s2p A A0 eqA n ltM x = a -> s2p A A0 eqA n ltM y = b -> ~ zerop A A0 eqA n ltM x -> exists r : poly A0 eqA ltM, In r (y :: Q) /\ divp A A0 eqA multA divA n ltM x r /\ ~ zerop A A0 eqA n ltM r.
intros a b Q H'; elim H'; auto.
intros x y H'0 H'1 x0 y0 H'2 H'3 H'4; exists y0; split; [ idtac | split ]; auto with datatypes.
generalize H'0 H'4; clear H'0 H'4; rewrite <- H'3; rewrite <- H'2; case x0; case y0; simpl in |- *; auto.
intros x1; case x1; simpl in |- *; auto.
intros H2 x2; case x2; auto.
intros t l H'5 H'6; inversion_clear H'6; auto.
intros t l H'0 x2; case x2; simpl in |- *; auto.
intros t0 l0 H'5 H'6; inversion_clear H'6; auto.
intros H5; apply divP_eqTerm_comp with (a := t) (1 := cs); auto.
cut (~ zeroP (A:=A) A0 eqA (n:=n) t); [ intros Z | idtac ]; auto.
apply divTerm_def with (nZb := Z); auto.
apply canonical_nzeroP with (ltM := ltM) (p := l); auto.
apply (eqTerm_sym _ _ _ _ _ _ _ _ _ cs n); auto.
generalize H'0 H'4; clear H'0 H'4; rewrite <- H'3; rewrite <- H'2; case x0; case y0; simpl in |- *; auto.
intros x1; case x1; simpl in |- *; auto.
intros H'0 x2; case x2; simpl in |- *; auto.
intros t l H'4 H'5; inversion_clear H'5.
intros x y z H'0 H'1 H'2 H'3 x0 y0 H'4 H'5 H'6.
cut (canonical A0 eqA ltM y); [ intros Z | idtac ].
2: apply canonical_reduce with (1 := cs) (3 := H'0); auto.
lapply (reduce_divp x0 (mks A A0 eqA n ltM y Z) Q); [ intros H'9 | idtac ]; auto.
2: rewrite H'4; simpl in |- *; auto.
case H'9; intros r E; case E; simpl in |- *; intros H'7 H'8; case H'8; intros H'10 H'11; clear H'8 E H'9.
case H'7; [ intros H'8; clear H'7 | intros H'8; clear H'7 ].
2: exists r; split; [ right | idtac ]; auto.
lapply H'2; [ intros H'7; lapply (H'7 (mks A A0 eqA n ltM y Z) y0); simpl in |- *; [ intros H'13; lapply H'13; [ intros H'14; lapply H'14; [ intros H'15; clear H'14 H'13 H'2 | clear H'14 H'13 H'2 ] | clear H'13 H'2 ] | clear H'2 ] | clear H'2 ]; auto.
case H'15; intros r0 E; case E; intros H'2 H'9; case H'9; intros H'12 H'13; clear H'9 E H'15.
exists r0; split; [ idtac | split ]; auto.
apply (divp_trans _ _ _ _ _ _ _ _ _ cs n ltM) with (y := r); auto.
rewrite <- H'8; auto.
generalize H'11; rewrite <- H'8.
Admitted.

Theorem reduceplus_divp : forall (a b : poly A0 eqA ltM) (Q : list (poly A0 eqA ltM)), reduceplus A A0 A1 eqA invA minusA multA divA eqA_dec n ltM ltM_dec Q (s2p A A0 eqA n ltM a) (s2p A A0 eqA n ltM b) -> ~ zerop A A0 eqA n ltM a -> exists r : poly A0 eqA ltM, In r (b :: Q) /\ divp A A0 eqA multA divA n ltM a r /\ ~ zerop A A0 eqA n ltM r.
intros a b Q H' H'0.
apply reduceplus_divp_lem with (a := s2p A A0 eqA n ltM a) (b := s2p A A0 eqA n ltM b); auto.
Admitted.

Theorem Cb_trans_cons : forall (L : list (poly A0 eqA ltM)) (p q : poly A0 eqA ltM), Cb A A0 eqA plusA multA eqA_dec n ltM ltM_dec q (p :: L) -> Cb A A0 eqA plusA multA eqA_dec n ltM ltM_dec p L -> Cb A A0 eqA plusA multA eqA_dec n ltM ltM_dec q L.
intros L p q H H0.
apply Cb_trans with (1 := cs) (b := p); auto.
apply Cb_cons_addEnd; auto.
