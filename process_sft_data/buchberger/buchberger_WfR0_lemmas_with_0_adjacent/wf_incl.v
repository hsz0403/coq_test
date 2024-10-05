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

Theorem wf_incl : well_founded RO.
unfold well_founded in |- *; intros.
apply Acc_intro; intros.
inversion H.
apply l1 with (bs := nf A A0 A1 eqA plusA invA minusA multA divA cs eqA_dec n ltM ltM_dec os a0 a :: nil) (ms := get_monL (nf A A0 A1 eqA plusA invA minusA multA divA cs eqA_dec n ltM ltM_dec os a0 a :: nil)); auto.
change (GRBar (mon n) (mdiv n) (get_mon (nf A A0 A1 eqA plusA invA minusA multA divA cs eqA_dec n ltM ltM_dec os a0 a) :: nil)) in |- *.
apply nilGRBar; auto.
apply dicksonL with (n := n); auto.
simpl in |- *; intros f H3; case H3; intros.
rewrite <- H4; auto.
elim H4.
red in |- *; intros H4; inversion H4; inversion H5.
