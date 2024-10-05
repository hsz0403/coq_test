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
apply CombLinear_canonical with (1 := cs) (3 := H'0); auto.
