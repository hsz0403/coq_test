Set Implicit Arguments.
Unset Strict Implicit.
Require Export point_cocyclicite.
Definition orthocentre (H A B C : PO) := (orthogonal (vec H A) (vec B C) /\ orthogonal (vec H B) (vec A C)) /\ orthogonal (vec H C) (vec A B).
Section Theoreme.
Parameter H A B C : PO.
Hypothesis triangle : ~ colineaire (vec A B) (vec A C).
Hypothesis H_orthocentre : orthocentre H A B C.
End Theoreme.

Lemma orthocentre_double : R (double (cons (vec H C) (vec H B))) (double (cons (vec A B) (vec A C))).
unfold orthocentre in H_orthocentre.
elim H_orthocentre; intros H0 H1; elim H0; intros H2 H3; clear H0 H_orthocentre; try exact H3.
apply transitive with (double (plus (cons (vec H C) (vec A B)) (plus (cons (vec A B) (vec A C)) (cons (vec A C) (vec H B))))).
apply R_double.
auto.
apply transitive with (plus (double (cons (vec H C) (vec A B))) (double (plus (cons (vec A B) (vec A C)) (cons (vec A C) (vec H B))))).
auto.
apply transitive with (plus (double (cons (vec H C) (vec A B))) (plus (double (cons (vec A B) (vec A C))) (double (cons (vec A C) (vec H B))))).
apply compatible; auto.
apply transitive with (plus pi (plus (double (cons (vec A B) (vec A C))) pi)).
apply compatible; auto.
apply compatible; auto.
cut (orthogonal (vec A C) (vec H B)); (intros; auto).
apply transitive with (plus (plus (double (cons (vec A B) (vec A C))) pi) pi).
auto.
apply transitive with (plus (double (cons (vec A B) (vec A C))) (plus pi pi)).
auto.
apply transitive with (plus (double (cons (vec A B) (vec A C))) zero).
apply compatible; auto.
apply transitive with (plus zero (double (cons (vec A B) (vec A C)))).
auto.
auto.
