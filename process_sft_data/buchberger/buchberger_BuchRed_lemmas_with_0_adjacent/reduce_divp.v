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
generalize c H'; rewrite <- H2; auto.
