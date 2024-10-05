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
intros H; apply Cb_id with (1 := cs); auto with datatypes.
