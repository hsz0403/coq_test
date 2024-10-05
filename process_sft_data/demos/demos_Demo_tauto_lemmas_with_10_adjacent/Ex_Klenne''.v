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

Theorem e2 : ~ ~ (A \/ ~ A).
Admitted.

Theorem e4 : ~ ~ (A \/ B -> A \/ B).
Admitted.

Theorem Ex_Klenne'' : ~ ~ ((forall n : nat, even n) \/ ~ (forall m : nat, even m)).
tauto.
