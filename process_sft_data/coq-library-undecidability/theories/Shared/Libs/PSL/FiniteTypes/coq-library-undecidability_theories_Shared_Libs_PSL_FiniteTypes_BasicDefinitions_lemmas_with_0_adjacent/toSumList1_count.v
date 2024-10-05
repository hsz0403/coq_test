From Undecidability.Shared.Libs.PSL Require Export Base.
Ltac dec := repeat (destruct Dec).
Ltac listComplete := intros x; simpl; dec; destruct x; try congruence.
Ltac deq x := destruct (Dec (x=x)) as [[] | isnotequal]; [> | contradict isnotequal; reflexivity] .
Fixpoint prodLists {X Y: Type} (A: list X) (B: list Y) {struct A} := match A with | nil => nil | cons x A' => map (fun y => (x,y)) B ++ prodLists A' B end.
Definition toOptionList {X: Type} (A: list X) := None :: map (@Some _) A .
Fixpoint count (X: Type) `{eq_dec X} (A: list X) (x: X) {struct A} : nat := match A with | nil => O | cons y A' => if Dec (x=y) then S(count A' x) else count A' x end.
Definition toSumList1 {X: Type} (Y: Type) (A: list X): list (X + Y) := map inl A.
Definition toSumList2 {Y: Type} (X: Type) (A: list Y): list (X + Y) := map inr A.

Lemma toSumList1_count (X: eqType) (x: X) (Y: eqType) (A: list X) : count (toSumList1 Y A) (inl x) = count A x .
Proof.
induction A; simpl; dec; congruence.
