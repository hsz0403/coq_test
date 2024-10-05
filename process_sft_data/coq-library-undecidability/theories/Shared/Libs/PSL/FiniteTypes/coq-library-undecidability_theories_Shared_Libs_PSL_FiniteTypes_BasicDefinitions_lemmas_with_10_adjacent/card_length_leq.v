From Undecidability.Shared.Libs.PSL Require Export Base.
Ltac dec := repeat (destruct Dec).
Ltac listComplete := intros x; simpl; dec; destruct x; try congruence.
Ltac deq x := destruct (Dec (x=x)) as [[] | isnotequal]; [> | contradict isnotequal; reflexivity] .
Fixpoint prodLists {X Y: Type} (A: list X) (B: list Y) {struct A} := match A with | nil => nil | cons x A' => map (fun y => (x,y)) B ++ prodLists A' B end.
Definition toOptionList {X: Type} (A: list X) := None :: map (@Some _) A .
Fixpoint count (X: Type) `{eq_dec X} (A: list X) (x: X) {struct A} : nat := match A with | nil => O | cons y A' => if Dec (x=y) then S(count A' x) else count A' x end.
Definition toSumList1 {X: Type} (Y: Type) (A: list X): list (X + Y) := map inl A.
Definition toSumList2 {Y: Type} (X: Type) (A: list Y): list (X + Y) := map inr A.

Lemma countIn (X:eqType) (x:X) A: count A x > 0 -> x el A.
Proof.
induction A.
-
cbn.
lia.
-
cbn.
dec.
+
intros.
left.
symmetry.
exact e.
+
intros.
right.
apply IHA.
Admitted.

Lemma InCount (X:eqType) (x:X) A: x el A -> count A x > 0.
Proof.
induction A.
-
intros [].
-
intros [[] | E]; cbn.
+
deq a.
lia.
+
specialize (IHA E).
Admitted.

Lemma count_in_equiv (X: eqType) (x:X) A : count A x > 0 <-> x el A.
Proof.
split.
-
apply countIn.
-
Admitted.

Lemma countApp (X: eqType) (x: X) (A B: list X) : count (A ++ x::B) x > 0.
Proof.
Admitted.

Lemma dupfreeCount (X: eqType) (x:X) (A: list X) : dupfree A -> x el A -> count A x = 1.
Proof.
intros D E.
induction D.
-
contradiction E.
-
cbn.
dec.
+
f_equal.
subst x0.
now apply notInZero.
+
Admitted.

Lemma toSumList1_count (X: eqType) (x: X) (Y: eqType) (A: list X) : count (toSumList1 Y A) (inl x) = count A x .
Proof.
Admitted.

Lemma toSumList2_count (X Y: eqType) (y: Y) (A: list Y): count (toSumList2 X A) (inr y) = count A y.
Proof.
Admitted.

Lemma toSumList1_missing (X Y: eqType) (y: Y) (A: list X): count (toSumList1 Y A ) (inr y) = 0.
Proof.
Admitted.

Lemma toSumList2_missing (X Y: eqType) (x: X) (A: list Y): count (toSumList2 X A ) (inl x) = 0.
Proof.
Admitted.

Lemma cons_incll (X: Type) (A B: list X) (x:X) : x::A <<= B -> A <<= B.
Proof.
unfold "<<=".
Admitted.

Lemma appendNil (X: Type) (A B: list X) : A ++ B = nil -> A = nil /\ B = nil.
Proof.
intros H.
assert (|A ++ B| = 0) by now rewrite H.
rewrite app_length in H0.
rewrite <- !length_zero_iff_nil.
Admitted.

Lemma countZero (X: eqType) (x: X) (A: list X) : count A x = 0 -> not (x el A).
Proof.
Admitted.

Lemma NullMul a b : a > 0 -> b > 0 -> a * b > 0.
Proof.
Admitted.

Lemma card_length_leq (X: eqType) (A: list X) : card A <= length A.
Proof.
induction A; auto.
cbn.
dec; lia.
