Set Implicit Arguments.
Unset Strict Implicit.
Require Export point_cocyclicite.
Hint Resolve colineaire_sym.
Hint Resolve colineaire_modulo_pi.
Hint Resolve orthogonal_opp.

Lemma projete_ortho_cote : forall A B C M P Q T : PO, colineaire (vec C A) (vec C Q) -> colineaire (vec P C) (vec P B) -> colineaire (vec B A) (vec B T) -> orthogonal (vec T M) (vec T B) -> orthogonal (vec P M) (vec P B) -> orthogonal (vec Q M) (vec Q C) -> R (double (cons (vec P Q) (vec P T))) (plus (double (cons (vec C A) (vec C M))) (double (cons (vec B M) (vec B A)))).
intros A B C M P Q S H H0 H1 H2 H3 H4; try assumption.
cut (R (double (cons (vec P Q) (vec P M))) (double (cons (vec C A) (vec C M)))); intros.
cut (R (double (cons (vec P S) (vec P M))) (double (cons (vec B A) (vec B M)))); intros.
apply transitive with (double (plus (cons (vec P Q) (vec P M)) (cons (vec P M) (vec P S)))); auto.
apply transitive with (plus (double (cons (vec P Q) (vec P M))) (double (cons (vec P M) (vec P S)))); auto.
apply compatible; auto.
apply transitive with (double (cons (vec B S) (vec B M))).
apply symetrique; apply (deux_rectangles (A:=M) (B:=B) (C:=S) (D:=P)); auto.
apply colineaire_modulo_pi; auto.
unfold colineaire in |- *.
apply transitive with (double zero); auto.
apply transitive with (double (cons (vec C Q) (vec C M))).
apply symetrique; apply (deux_rectangles (A:=M) (B:=C) (C:=Q) (D:=P)); auto.
apply orthogonal_colineaire with (vec P B); auto.
apply colineaire_modulo_pi; auto.
unfold colineaire in |- *.
apply transitive with (double zero); auto.
