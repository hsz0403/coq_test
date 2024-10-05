Parameter A B C : Prop.
Parameter even : nat -> Prop.
Parameter P : nat -> Prop.
Section club.
Variable Scottish RedSocks WearKilt Married GoOutSunday : Prop.
Hypothesis rule1 : ~ Scottish -> RedSocks.
Hypothesis rule2 : WearKilt \/ ~ RedSocks.
Hypothesis rule3 : Married -> ~ GoOutSunday.
Hypothesis rule4 : GoOutSunday <-> Scottish.
Hypothesis rule5 : WearKilt -> Scottish /\ Married.
Hypothesis rule6 : Scottish -> WearKilt.
End club.

Theorem Ex_Wallen : (A -> B /\ C) -> (A -> B) \/ (A -> C).
Admitted.

Theorem Ex_Klenne : ~ ~ (A \/ ~ A).
Admitted.

Theorem Ex_Klenne' : forall n : nat, ~ ~ (even n \/ ~ even n).
intro.
Admitted.

Theorem Ex_Klenne'' : ~ ~ ((forall n : nat, even n) \/ ~ (forall m : nat, even m)).
Admitted.

Theorem Intu : (forall x : nat, P x) /\ B -> (forall y : nat, P y) /\ P 0 \/ B /\ P 0.
Admitted.

Lemma NoMember : False.
Admitted.

Theorem tauto : (forall x : nat, P x) -> forall y : nat, P y.
Admitted.

Theorem tauto1 : A -> A.
Admitted.

Theorem tauto2 : (A -> B -> C) -> (A -> B) -> A -> C.
Admitted.

Theorem a : forall (x0 : A \/ B) (x1 : B /\ C), A -> B.
Admitted.

Theorem a2 : (A -> B /\ C) -> (A -> B) \/ (A -> C).
Admitted.

Theorem a4 : ~ A -> ~ A.
Admitted.

Theorem e4 : ~ ~ (A \/ B -> A \/ B).
Admitted.

Theorem y0 : forall (x0 : A) (x1 : ~ A) (x2 : A -> B) (x3 : A \/ B) (x4 : A /\ B), A -> False.
Admitted.

Theorem y1 : forall x0 : (A /\ B) /\ C, B.
Admitted.

Theorem y2 : forall (x0 : A) (x1 : B), C \/ B.
Admitted.

Theorem y3 : forall x0 : A /\ B, B /\ A.
Admitted.

Theorem y5 : forall x0 : A \/ B, B \/ A.
Admitted.

Theorem y6 : forall (x0 : A -> B) (x1 : A), B.
Admitted.

Theorem y7 : forall (x0 : A /\ B -> C) (x1 : B) (x2 : A), C.
Admitted.

Theorem y8 : forall (x0 : A \/ B -> C) (x1 : A), C.
Admitted.

Theorem y9 : forall (x0 : A \/ B -> C) (x1 : B), C.
Admitted.

Theorem y10 : forall (x0 : (A -> B) -> C) (x1 : B), C.
Admitted.

Theorem e2 : ~ ~ (A \/ ~ A).
tauto.
