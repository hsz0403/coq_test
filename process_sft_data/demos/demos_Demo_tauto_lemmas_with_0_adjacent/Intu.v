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

Theorem Intu : (forall x : nat, P x) /\ B -> (forall y : nat, P y) /\ P 0 \/ B /\ P 0.
intuition.
