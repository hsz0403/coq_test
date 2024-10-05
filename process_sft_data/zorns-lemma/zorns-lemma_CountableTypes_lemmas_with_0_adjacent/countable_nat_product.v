Require Export FiniteTypes Relation_Definitions ZArith QArith IndexedFamilies.
Require Import InfiniteTypes CSB DecidableDec FunctionalExtensionality ProofIrrelevance DependentTypeChoice ClassicalChoice Arith ArithRing.
Local Close Scope Q_scope.
Set Asymmetric Patterns.
Inductive CountableT (X : Type) : Prop := | intro_nat_injection (f : X -> nat) : injective f -> CountableT X.
Definition Countable {X : Type} (S : Ensemble X) : Prop := CountableT {x:X | In S x}.

Lemma countable_nat_product: CountableT (nat * nat).
Proof.
pose (sum_1_to_n := fix sum_1_to_n n:nat := match n with | O => O | S m => (sum_1_to_n m) + n end).
exists (fun p:nat*nat => let (m,n):=p in (sum_1_to_n (m+n)) + n).
assert (forall m n:nat, m<n -> sum_1_to_n m + m < sum_1_to_n n).
-
intros.
induction H.
+
simpl.
auto with arith.
+
apply lt_trans with (sum_1_to_n m0); trivial.
assert (sum_1_to_n m0 + 0 < sum_1_to_n m0 + S m0) by auto with arith.
assert (sum_1_to_n m0 + 0 = sum_1_to_n m0) by auto with arith.
now rewrite H1 in H0.
-
intros [x1 y1] [x2 y2] H0.
case (lt_eq_lt_dec (x1+y1) (x2+y2)); intro.
+
case s; intro.
*
assert (sum_1_to_n (x1+y1) + y1 < sum_1_to_n (x2+y2) + y2).
**
apply le_lt_trans with (sum_1_to_n (x1+y1) + (x1+y1)).
***
assert (sum_1_to_n (x1+y1) + (x1+y1) = (sum_1_to_n (x1+y1) + y1) + x1); [ ring | auto with arith ].
***
apply lt_le_trans with (sum_1_to_n (x2+y2)); [ apply H |]; auto with arith.
**
rewrite H0 in H1.
contradict H1.
auto with arith.
*
assert (y1=y2).
**
rewrite e in H0.
now apply plus_reg_l in H0.
**
f_equal; trivial.
rewrite H1, plus_comm, (plus_comm x2 y2) in e.
now apply plus_reg_l in e.
+
assert (sum_1_to_n (x2+y2) + y2 < sum_1_to_n (x1+y1) + y1).
*
apply le_lt_trans with (sum_1_to_n (x2+y2) + (x2+y2)), lt_le_trans with (sum_1_to_n (x1+y1)); auto with arith.
*
rewrite H0 in H1.
contradict H1.
auto with arith.
