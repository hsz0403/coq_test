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

Theorem zerop_elim_cb : forall (L : list (poly A0 eqA ltM)) (p q : poly A0 eqA ltM), zerop A A0 eqA n ltM p -> Cb A A0 eqA plusA multA eqA_dec n ltM ltM_dec q (p :: L) -> Cb A A0 eqA plusA multA eqA_dec n ltM ltM_dec q L.
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

Theorem zerop_nf_cb : forall (L : list (poly A0 eqA ltM)) (p : poly A0 eqA ltM), zerop A A0 eqA n ltM (nf A A0 A1 eqA plusA invA minusA multA divA cs eqA_dec n ltM ltM_dec os p L) -> Cb A A0 eqA plusA multA eqA_dec n ltM ltM_dec p L.
intros L p H'.
apply zerop_elim_cb with (p := nf A A0 A1 eqA plusA invA minusA multA divA cs eqA_dec n ltM ltM_dec os p L); auto.
Admitted.

Definition redacc : list (poly A0 eqA ltM) -> list (poly A0 eqA ltM) -> list (poly A0 eqA ltM).
intros H'; elim H'.
intros L; exact (nil (A:=poly A0 eqA ltM)).
intros a p Rec Acc.
apply LetP with (A := poly A0 eqA ltM) (h := nf A A0 A1 eqA plusA invA minusA multA divA cs eqA_dec n ltM ltM_dec os a (p ++ Acc)).
intros u H'0; case (zerop_dec A A0 eqA n ltM u); intros Z.
exact (Rec Acc).
Admitted.

Theorem redacc_cb : forall (L1 L2 : list (poly A0 eqA ltM)) (p : poly A0 eqA ltM), In p (redacc L1 L2) -> Cb A A0 eqA plusA multA eqA_dec n ltM ltM_dec p (L1 ++ L2).
intros L1; elim L1; auto.
simpl in |- *; auto.
intros L2 p H; elim H.
simpl in |- *; unfold LetP in |- *; intros a l H' L2 p.
case (zerop_dec A A0 eqA n ltM (nf A A0 A1 eqA plusA invA minusA multA divA cs eqA_dec n ltM ltM_dec os a (l ++ L2))).
intros H'0 H'1.
apply Cb_incl with (P := l ++ L2) (1 := cs); auto.
simpl in |- *; auto.
simpl in |- *.
intros H'0 H'1; case H'1; [ intros H'2; rewrite <- H'2; clear H'1 | intros H'2; clear H'1 ]; auto.
apply Cb_cons; auto.
apply Cb_trans_cons with (p := nf A A0 A1 eqA plusA invA minusA multA divA cs eqA_dec n ltM ltM_dec os a (l ++ L2)); auto.
apply Cb_incl with (1 := cs) (P := l ++ nf A A0 A1 eqA plusA invA minusA multA divA cs eqA_dec n ltM ltM_dec os a (l ++ L2) :: L2); auto.
change (incl (l ++ nf A A0 A1 eqA plusA invA minusA multA divA cs eqA_dec n ltM ltM_dec os a (l ++ L2) :: L2) (nf A A0 A1 eqA plusA invA minusA multA divA cs eqA_dec n ltM ltM_dec os a (l ++ L2) :: a :: l ++ L2)) in |- *.
apply incl_app; auto with datatypes.
Admitted.

Theorem Red_cb : forall (L : list (poly A0 eqA ltM)) (p : poly A0 eqA ltM), In p (Red L) -> Cb A A0 eqA plusA multA eqA_dec n ltM ltM_dec p L.
unfold Red in |- *.
intros L p H'.
generalize (redacc_cb L nil); simpl in |- *; auto.
Admitted.

Theorem cb_redacc : forall (L1 L2 : list (poly A0 eqA ltM)) (p : poly A0 eqA ltM), In p L1 -> Cb A A0 eqA plusA multA eqA_dec n ltM ltM_dec p (redacc L1 L2 ++ L2).
intros L1; elim L1; simpl in |- *; auto.
intros L2 p H'; elim H'; auto.
unfold LetP in |- *.
intros a l H' L2 p H'0; case H'0; [ intros H'1; rewrite H'1; clear H'0 | intros H'1; clear H'0 ]; auto.
case (zerop_dec A A0 eqA n ltM (nf A A0 A1 eqA plusA invA minusA multA divA cs eqA_dec n ltM ltM_dec os p (l ++ L2))); auto.
intros H'0.
apply Cb_comp with (L1 := l ++ L2); auto.
intros p0 H'2.
lapply (in_app_or l L2 p0); auto.
intros H'3; case H'3; auto.
intros H'4; apply Cb_id with (1 := cs); auto with datatypes.
intros H'0.
2: case (zerop_dec A A0 eqA n ltM (nf A A0 A1 eqA plusA invA minusA multA divA cs eqA_dec n ltM ltM_dec os a (l ++ L2))); auto.
2: intros H'0.
2: apply Cb_incl with (1 := cs) (P := redacc l (nf A A0 A1 eqA plusA invA minusA multA divA cs eqA_dec n ltM ltM_dec os a (l ++ L2) :: L2) ++ nf A A0 A1 eqA plusA invA minusA multA divA cs eqA_dec n ltM ltM_dec os a (l ++ L2) :: L2); auto with datatypes.
2: intros a0 H; case (in_app_or _ _ _ H); auto with datatypes.
2: simpl in |- *; intros H1; case H1; auto with datatypes.
apply Cb_compo with (L1 := nf A A0 A1 eqA plusA invA minusA multA divA cs eqA_dec n ltM ltM_dec os p (l ++ L2) :: l ++ L2); simpl in |- *; auto.
apply Cb_nf; auto.
intros q H'2; case H'2; [ intros H'3; rewrite <- H'3; clear H'2 | intros H'3; clear H'2 ]; auto with datatypes.
apply Cb_id with (1 := cs); auto with datatypes.
case (in_app_or _ _ _ H'3); auto with datatypes.
intros H'2.
apply Cb_incl with (1 := cs) (P := redacc l (nf A A0 A1 eqA plusA invA minusA multA divA cs eqA_dec n ltM ltM_dec os p (l ++ L2) :: L2) ++ nf A A0 A1 eqA plusA invA minusA multA divA cs eqA_dec n ltM ltM_dec os p (l ++ L2) :: L2); auto with datatypes.
intros a0 H; case (in_app_or _ _ _ H); auto with datatypes.
simpl in |- *; intros H1; case H1; auto with datatypes.
Admitted.

Theorem Cb_Red : forall (L : list (poly A0 eqA ltM)) (p : poly A0 eqA ltM), In p L -> Cb A A0 eqA plusA multA eqA_dec n ltM ltM_dec p (Red L).
intros L p H'.
lapply (cb_redacc L nil p); [ intros H'3; generalize H'3 | idtac ]; simpl in |- *; auto.
Admitted.

Theorem cb_Red_cb1 : forall (p : poly A0 eqA ltM) (L : list (poly A0 eqA ltM)), Cb A A0 eqA plusA multA eqA_dec n ltM ltM_dec p L -> Cb A A0 eqA plusA multA eqA_dec n ltM ltM_dec p (Red L).
intros p L H'.
apply Cb_compo with (L1 := L); auto.
intros q H'0.
Admitted.

Theorem cb_Red_cb2 : forall (p : poly A0 eqA ltM) (L : list (poly A0 eqA ltM)), Cb A A0 eqA plusA multA eqA_dec n ltM ltM_dec p (Red L) -> Cb A A0 eqA plusA multA eqA_dec n ltM ltM_dec p L.
intros p L H'.
apply Cb_compo with (L1 := Red L); auto.
intros q H'0.
Admitted.

Theorem divp_id : forall p : poly A0 eqA ltM, ~ zerop A A0 eqA n ltM p -> divp A A0 eqA multA divA n ltM p p.
intros p; case p; auto.
intros x; case x; simpl in |- *; auto.
intros a l H' J.
cut (~ zeroP (A:=A) A0 eqA (n:=n) a); [ intros Z | idtac ].
apply divTerm_def with (nZb := Z).
apply canonical_nzeroP with (p := l) (ltM := ltM); auto.
apply (eqTerm_trans _ _ _ _ _ _ _ _ _ cs n) with (y := multTerm (A:=A) multA (n:=n) (T1 A1 n) a); auto.
apply (eqTerm_sym _ _ _ _ _ _ _ _ _ cs n); auto.
Admitted.

Theorem Red_divp : forall (L : list (poly A0 eqA ltM)) (p : poly A0 eqA ltM), In p L -> ~ zerop A A0 eqA n ltM p -> exists q : poly A0 eqA ltM, In q (Red L) /\ divp A A0 eqA multA divA n ltM p q /\ ~ zerop A A0 eqA n ltM q.
intros L p H' H'0.
lapply (redacc_divp L nil p); auto.
simpl in |- *; auto.
rewrite <- app_nil_end; auto.
Admitted.

Theorem Red_grobner : forall L : list (poly A0 eqA ltM), Grobner A A0 A1 eqA plusA invA minusA multA divA eqA_dec n ltM ltM_dec L -> Grobner A A0 A1 eqA plusA invA minusA multA divA eqA_dec n ltM ltM_dec (Red L).
intros L H'.
apply def_grobner; auto.
intros p H'0.
lapply (grobner_def L); [ intros H'2; lapply (H'2 p); [ intros H'4 | idtac ] | idtac ]; auto.
case H'4; auto.
intros H'1; case H'1; intros q E; clear H'1.
right.
apply divp_reduce1 with (L1 := L) (q := q); auto.
intros r1 H'1 H'3.
lapply (Red_divp L r1); [ intros H'7; lapply H'7; [ intros H'8; clear H'7 | clear H'7 ] | idtac ]; auto.
case H'8; intros q0 E0; case E0; intros H'5 H'6; case H'6; intros H'7 H'9; clear H'6 E0 H'8.
exists q0; split; auto.
Admitted.

Theorem redbuch_stable : forall P : list (poly A0 eqA ltM), stable A A0 eqA plusA multA eqA_dec n ltM ltM_dec P (redbuch P).
intros P.
cut (stable A A0 eqA plusA multA eqA_dec n ltM ltM_dec P (buch A A0 A1 eqA plusA invA minusA multA divA cs eqA_dec n ltM ltM_dec os P)).
intros H'0; inversion H'0; auto.
apply stable0; unfold redbuch in |- *; auto.
intros a H'.
apply cb_Red_cb1; auto.
intros a H'.
apply H0; auto.
apply cb_Red_cb2; auto.
Admitted.

Theorem redbuch_Grobner : forall P : list (poly A0 eqA ltM), Grobner A A0 A1 eqA plusA invA minusA multA divA eqA_dec n ltM ltM_dec (redbuch P).
intros P.
unfold redbuch in |- *.
apply Red_grobner; auto.
Admitted.

Theorem redacc_divp : forall (L1 L2 : list (poly A0 eqA ltM)) (p : poly A0 eqA ltM), ~ zerop A A0 eqA n ltM p -> In p (L1 ++ L2) -> exists q : poly A0 eqA ltM, In q (redacc L1 L2 ++ L2) /\ divp A A0 eqA multA divA n ltM p q /\ ~ zerop A A0 eqA n ltM q.
intros L1; elim L1; simpl in |- *; auto.
intros L2 p H' H'0; exists p; split; auto.
split; auto.
apply divp_id; auto.
unfold LetP in |- *.
intros a l H' L2 p H'0 H'1; case H'1; [ intros H'2; rewrite <- H'2; clear H'1 | intros H'2; clear H'1 ]; auto.
case (zerop_dec A A0 eqA n ltM (nf A A0 A1 eqA plusA invA minusA multA divA cs eqA_dec n ltM ltM_dec os a (l ++ L2))); simpl in |- *; auto.
intros Z1.
lapply (nf_divp_zero a (l ++ L2)); [ intros H'5; lapply H'5; [ intros H'6; clear H'5 | clear H'5 ] | idtac ]; auto.
case H'6; intros q E; case E; intros H'3 H'4; case H'4; intros H'5 H'7; clear H'4 E H'6.
lapply (H' L2 q); [ intros H'8; lapply H'8; [ intros H'9; clear H'8 | clear H'8 ] | idtac ]; auto.
case H'9; intros q0 E; case E; intros H'4 H'6; case H'6; intros H'8 H'10; clear H'6 E H'9.
exists q0; split; [ idtac | split ]; auto.
apply (divp_trans _ _ _ _ _ _ _ _ _ cs n ltM) with (y := q); auto.
rewrite H'2; auto.
intros Z1.
lapply (nf_divp a (l ++ L2)); [ intros H'5; lapply H'5; [ intros H'6; clear H'5 | clear H'5 ] | idtac ]; auto.
case H'6; intros q E; case E; intros H'3 H'4; case H'4; intros H'5 H'7; clear H'4 E H'6.
simpl in H'3.
case H'3; [ intros H'4; clear H'3 | intros H'4; clear H'3 ].
exists q; split; [ idtac | split ]; auto.
lapply (H' (nf A A0 A1 eqA plusA invA minusA multA divA cs eqA_dec n ltM ltM_dec os a (l ++ L2) :: L2) q); [ intros H'8; lapply H'8; [ intros H'9; clear H'8 | clear H'8 ] | idtac ]; auto.
case H'9; intros q0 E; case E; intros H'3 H'6; case H'6; intros H'8 H'10; clear H'6 E H'9.
exists q0; split; [ idtac | split ]; auto.
case (in_app_or _ _ _ H'3); auto.
simpl in |- *; auto with datatypes.
simpl in |- *; intros H'6; case H'6; [ intros H'9; clear H'6 | intros H'9; clear H'6 ]; auto.
auto with datatypes.
apply (divp_trans _ _ _ _ _ _ _ _ _ cs n ltM) with (y := q); auto.
case (in_app_or _ _ _ H'4); auto with datatypes.
rewrite H'2; auto.
case (zerop_dec A A0 eqA n ltM (nf A A0 A1 eqA plusA invA minusA multA divA cs eqA_dec n ltM ltM_dec os a (l ++ L2))); simpl in |- *; auto.
intros Z1.
case (in_app_or _ _ _ H'2); auto.
intros H'3.
lapply (H' (nf A A0 A1 eqA plusA invA minusA multA divA cs eqA_dec n ltM ltM_dec os a (l ++ L2) :: L2) p); [ intros H'6; lapply H'6; [ intros H'7; clear H'6 | clear H'6 ] | idtac ]; auto with datatypes.
case H'7; intros q E; case E; intros H'4 H'5; case H'5; intros H'6 H'8; clear H'5 E H'7.
exists q; split; auto.
case (in_app_or _ _ _ H'4); auto with datatypes.
simpl in |- *; auto.
intros H; case H; intros H1; auto with datatypes.
intros H; exists p; split; [ right | idtac ]; auto with datatypes.
split; auto.
apply divp_id; auto.
