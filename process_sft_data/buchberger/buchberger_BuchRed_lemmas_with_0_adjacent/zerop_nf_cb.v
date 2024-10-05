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

Theorem zerop_nf_cb : forall (L : list (poly A0 eqA ltM)) (p : poly A0 eqA ltM), zerop A A0 eqA n ltM (nf A A0 A1 eqA plusA invA minusA multA divA cs eqA_dec n ltM ltM_dec os p L) -> Cb A A0 eqA plusA multA eqA_dec n ltM ltM_dec p L.
intros L p H'.
apply zerop_elim_cb with (p := nf A A0 A1 eqA plusA invA minusA multA divA cs eqA_dec n ltM ltM_dec os p L); auto.
apply Cb_nf.
