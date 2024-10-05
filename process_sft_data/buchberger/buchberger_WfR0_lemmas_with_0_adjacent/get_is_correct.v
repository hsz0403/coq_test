Require Import List.
Require Import ListProps.
Require Import Bar.
Require Import Dickson.
Require Import Monomials.
Require Export BuchAux.
Section thRO.
Load hCoefStructure.
Load hOrderStructure.
Load hBuchAux.
Definition get_mon : poly A0 eqA ltM -> mon n.
intros sp; case sp.
intros x H'; case x.
exact (M1 n).
intros a H'1; exact (T2M a).
Defined.
Definition get_monL : list (poly A0 eqA ltM) -> list (mon n) := map get_mon.
Inductive RO : list (poly A0 eqA ltM) -> list (poly A0 eqA ltM) -> Prop := RO0 : forall (a : poly A0 eqA ltM) (P : list (poly A0 eqA ltM)), ~ zerop A A0 eqA n ltM (nf A A0 A1 eqA plusA invA minusA multA divA cs eqA_dec n ltM ltM_dec os a P) -> RO (P ++ nf A A0 A1 eqA plusA invA minusA multA divA cs eqA_dec n ltM ltM_dec os a P :: nil) P.
Definition BadM (l : list (mon n)) := GoodR (mon n) (mdiv n) l -> False.
End thRO.

Theorem get_is_correct : forall (a b : poly A0 eqA ltM) (P : list (poly A0 eqA ltM)), ~ zerop A A0 eqA n ltM (nf A A0 A1 eqA plusA invA minusA multA divA cs eqA_dec n ltM ltM_dec os a P) -> In b P -> ~ zerop A A0 eqA n ltM b -> ~ mdiv n (get_mon b) (get_mon (nf A A0 A1 eqA plusA invA minusA multA divA cs eqA_dec n ltM ltM_dec os a P)).
intros a b P H' H'0 H'1.
cut (irreducible A A0 A1 eqA invA minusA multA divA eqA_dec n ltM ltM_dec P (s2p A A0 eqA n ltM (nf A A0 A1 eqA plusA invA minusA multA divA cs eqA_dec n ltM ltM_dec os a P))).
2: try exact (nf_irreducible a P); auto.
generalize H'; case (nf A A0 A1 eqA plusA invA minusA multA divA cs eqA_dec n ltM ltM_dec os a P); simpl in |- *; auto.
intros x; case x; simpl in |- *.
intros H'2 H'3; elim H'3; auto.
intros a0 l H'2 H'3 H'4; red in |- *; intros H'5; red in H'4.
red in H'4.
generalize H'0 H'1 H'5; case b.
intros x0; case x0; simpl in |- *.
intros o H'6 H'7; elim H'7; auto.
intros a1 l0 o H'6 H'7 H'8.
cut (~ zeroP (A:=A) A0 eqA (n:=n) a1); [ intros nZa1 | idtac ].
apply H'4 with (q := spminusf A A0 A1 eqA invA minusA multA divA eqA_dec n ltM ltM_dec a0 a1 nZa1 l l0); auto.
change (reduce A A0 A1 eqA invA minusA multA divA eqA_dec n ltM ltM_dec P (pX a0 l) (spminusf A A0 A1 eqA invA minusA multA divA eqA_dec n ltM ltM_dec a0 a1 nZa1 l l0)) in |- *.
apply reducetop_sp with (1 := cs) (b := a1) (nZb := nZa1) (q := l0); auto.
change (inPolySet A A0 eqA n ltM (s2p A A0 eqA n ltM (mks A A0 eqA n ltM (pX a1 l0) o)) P) in |- *.
apply in_inPolySet; auto.
simpl in |- *; auto.
red in |- *; intros H'9; inversion H'9.
apply divTerm_def with (nZb := nZa1); auto.
apply canonical_nzeroP with (ltM := ltM) (p := l); auto.
apply divTerm_on_plusM_minusM with (1 := cs); auto.
apply canonical_nzeroP with (ltM := ltM) (p := l); auto.
simpl in |- *; auto.
apply sym_equal; auto.
apply mdiv_div; auto.
apply canonical_nzeroP with (ltM := ltM) (p := l0); auto.
apply nf_irreducible; auto.
