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
apply Cb_cons; auto.
