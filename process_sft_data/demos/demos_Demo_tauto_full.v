Parameter A B C : Prop.
Parameter even : nat -> Prop.
Parameter P : nat -> Prop.
Theorem Ex_Wallen : (A -> B /\ C) -> (A -> B) \/ (A -> C).
tauto.
Qed.
Theorem Ex_Klenne : ~ ~ (A \/ ~ A).
tauto.
Qed.
Theorem Ex_Klenne' : forall n : nat, ~ ~ (even n \/ ~ even n).
intro.
tauto.
Qed.
Theorem Ex_Klenne'' : ~ ~ ((forall n : nat, even n) \/ ~ (forall m : nat, even m)).
tauto.
Qed.
Theorem Intu : (forall x : nat, P x) /\ B -> (forall y : nat, P y) /\ P 0 \/ B /\ P 0.
intuition.
Qed.
Section club.
Variable Scottish RedSocks WearKilt Married GoOutSunday : Prop.
Hypothesis rule1 : ~ Scottish -> RedSocks.
Hypothesis rule2 : WearKilt \/ ~ RedSocks.
Hypothesis rule3 : Married -> ~ GoOutSunday.
Hypothesis rule4 : GoOutSunday <-> Scottish.
Hypothesis rule5 : WearKilt -> Scottish /\ Married.
Hypothesis rule6 : Scottish -> WearKilt.
Lemma NoMember : False.
tauto.
Qed.
End club.
Theorem tauto : (forall x : nat, P x) -> forall y : nat, P y.
tauto.
Qed.
Theorem tauto1 : A -> A.
tauto.
Qed.
Theorem tauto2 : (A -> B -> C) -> (A -> B) -> A -> C.
tauto.
Qed.
Theorem a : forall (x0 : A \/ B) (x1 : B /\ C), A -> B.
tauto.
Qed.
Theorem a2 : (A -> B /\ C) -> (A -> B) \/ (A -> C).
tauto.
Qed.
Theorem a4 : ~ A -> ~ A.
tauto.
Qed.
Theorem e2 : ~ ~ (A \/ ~ A).
tauto.
Qed.
Theorem e4 : ~ ~ (A \/ B -> A \/ B).
tauto.
Qed.
Theorem y0 : forall (x0 : A) (x1 : ~ A) (x2 : A -> B) (x3 : A \/ B) (x4 : A /\ B), A -> False.
tauto.
Qed.
Theorem y1 : forall x0 : (A /\ B) /\ C, B.
tauto.
Qed.
Theorem y2 : forall (x0 : A) (x1 : B), C \/ B.
tauto.
Qed.
Theorem y3 : forall x0 : A /\ B, B /\ A.
tauto.
Qed.
Theorem y5 : forall x0 : A \/ B, B \/ A.
tauto.
Qed.
Theorem y6 : forall (x0 : A -> B) (x1 : A), B.
tauto.
Qed.
Theorem y7 : forall (x0 : A /\ B -> C) (x1 : B) (x2 : A), C.
tauto.
Qed.
Theorem y8 : forall (x0 : A \/ B -> C) (x1 : A), C.
tauto.
Qed.
Theorem y9 : forall (x0 : A \/ B -> C) (x1 : B), C.
tauto.
Qed.
Theorem y10 : forall (x0 : (A -> B) -> C) (x1 : B), C.
tauto.
Qed.