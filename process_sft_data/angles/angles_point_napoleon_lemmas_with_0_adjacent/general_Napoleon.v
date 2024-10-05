Set Implicit Arguments.
Unset Strict Implicit.
Require Export point_cocyclicite.
Hint Resolve colineaire_sym.
Hint Resolve colineaire_modulo_pi.
Hint Resolve orthogonal_opp.
Hint Resolve double_orthogonal.
Hint Resolve critere_orthogonal critere_orthogonal_reciproque.
Definition bissectrice (I A B C : PO) := R (cons (vec A B) (vec A I)) (cons (vec A I) (vec A C)).
Hint Resolve bissectrice_double.
Hint Resolve bissectrice_unicite.
Hint Resolve bissectrice_direction.
Hint Resolve orthogonal_bissectrice.
Hint Resolve bissectrice_droite.
Definition milieu (I B C : PO) := colineaire (vec B I) (vec B C) /\ (forall A : PO, isocele A B C -> bissectrice I A B C).
Axiom existence_milieu : forall B C : PO, exists I : PO, milieu I B C.
Axiom point_aligne : forall A B C : PO, colineaire (vec A B) (vec C B) -> colineaire (vec A B) (vec A C).

Theorem general_Napoleon : forall A B C P0 Q T O1 O2 I : PO, circonscrit T A B O1 -> circonscrit I A B O1 -> circonscrit Q A C O2 -> circonscrit I A C O2 -> ~ colineaire (vec P0 B) (vec P0 C) -> R (plus (cons (vec P0 C) (vec P0 B)) (plus (cons (vec T B) (vec T A)) (cons (vec Q A) (vec Q C)))) pi -> exists O3 : PO, R (double (cons (vec O1 O2) (vec O1 O3))) (double (cons (vec T A) (vec T B))) /\ R (double (cons (vec O1 O3) (vec O2 O3))) (double (cons (vec P0 B) (vec P0 C))) /\ R (double (cons (vec O1 O2) (vec O2 O3))) (double (cons (vec Q A) (vec Q C))).
intros A B C P Q T O1 O2 I H H0 H1 H2 H3 H4; try assumption.
cut (sont_cocycliques P B C I); intros.
elim cocyclicite_six with (A := B) (B := C) (C := P) (D := I); [ intros O3 H6; elim H6; intros H7 H8; clear H6; try exact H7 | auto ].
elim H7; intros H6 H9; clear H7; try exact H9.
exists O3.
elim circonscrit_3centres with (A := A) (B := B) (C := C) (O1 := O1) (O2 := O2) (O3 := O3) (I := I); [ try exact H7 | idtac | idtac | idtac ].
intros H7 H10; elim H10; intros H11 H12; clear H10; try exact H11.
split; [ idtac | split; [ try assumption | idtac ] ].
apply transitive with (double (cons (vec I A) (vec I B))); auto.
unfold circonscrit in H9, H6, H2, H1, H0, H.
elim H; intros H10 H13; elim H13; intros H14 H15; clear H13 H; try exact H14.
elim H0; intros H H13; elim H13; intros H16 H17; clear H13 H0; try exact H16.
apply cocyclique with O1; auto.
apply transitive with (double (cons (vec I B) (vec I C))); auto.
unfold circonscrit in H9, H6, H2, H1, H0, H.
elim H9; intros H10 H13; elim H13; intros H14 H15; clear H13 H9; try exact H14.
elim H6; intros H9 H13; elim H13; intros H16 H17; clear H13 H6; try exact H16.
apply cocyclique with O3; auto.
apply transitive with (double (cons (vec I A) (vec I C))); auto.
unfold circonscrit in H9, H6, H2, H1, H0, H.
elim H2; intros H10 H13; elim H13; intros H14 H15; clear H13 H2; try exact H14.
elim H1; intros H2 H13; elim H13; intros H16 H17; clear H13 H1; try exact H16.
apply cocyclique with O2; auto.
assumption.
assumption.
assumption.
apply (concours_3circonscrits (A:=A) (B:=B) (C:=C) (P:=P) (Q:=Q) (T:=T) (O1:=O1) (O2:=O2) (I:=I)); auto.
