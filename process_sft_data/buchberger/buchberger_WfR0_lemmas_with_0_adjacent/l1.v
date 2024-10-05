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

Lemma l1 : forall (cs : list (poly A0 eqA ltM)) (ms : list (mon n)), Bar (mon n) (GoodR (mon n) (mdiv n)) ms -> forall bs : list (poly A0 eqA ltM), ms = get_monL bs -> (forall f : poly A0 eqA ltM, In f bs -> ~ zerop A A0 eqA n ltM f) -> BadM ms -> Acc RO (cs ++ rev bs).
intros cs1 ms1 H; elim H; auto.
intros l H' bs H'0 H'1 H'2.
case H'2; auto.
intros l H' H'0 bs Heq Hnz H'1; auto.
apply Acc_intro; auto.
intros y H'2; inversion H'2; auto.
rewrite <- ass_app.
change (Acc RO (cs1 ++ rev bs ++ rev (nf A A0 A1 eqA plusA invA minusA multA divA cs eqA_dec n ltM ltM_dec os a (cs1 ++ rev bs) :: nil))) in |- *.
rewrite <- distr_rev; simpl in |- *.
change (Acc RO (cs1 ++ rev (nf A A0 A1 eqA plusA invA minusA multA divA cs eqA_dec n ltM ltM_dec os a (cs1 ++ rev bs) :: bs))) in |- *.
apply H'0 with (a := get_mon (nf A A0 A1 eqA plusA invA minusA multA divA cs eqA_dec n ltM ltM_dec os a (cs1 ++ rev bs))); unfold get_monL in |- *; try rewrite Heq; simpl in |- *; auto.
intros f H'3; elim H'3; [ intros H'4; rewrite <- H'4; clear H'3 | intros H'4; clear H'3 ]; auto.
apply tdivGoodP with (trm := mon n) (tdiv := mdiv n); auto.
rewrite <- Heq; auto.
intros g.
intros H'3; cut (ex (fun b : poly A0 eqA ltM => g = get_mon b /\ In b bs)).
intros H'4; elim H'4; intros b E; elim E; intros H'5 H'6; rewrite H'5; clear E H'4; auto.
apply get_is_correct; auto.
apply in_or_app; apply or_intror; apply in_rev; rewrite rev_involutive; auto.
apply map_in; auto.
