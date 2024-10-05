Require Export FiniteTypes Relation_Definitions ZArith QArith IndexedFamilies.
Require Import InfiniteTypes CSB DecidableDec FunctionalExtensionality ProofIrrelevance DependentTypeChoice ClassicalChoice Arith ArithRing.
Local Close Scope Q_scope.
Set Asymmetric Patterns.
Inductive CountableT (X : Type) : Prop := | intro_nat_injection (f : X -> nat) : injective f -> CountableT X.
Definition Countable {X : Type} (S : Ensemble X) : Prop := CountableT {x:X | In S x}.

Lemma Q_countable: CountableT Q.
Proof.
destruct countable_nat_product as [f], positive_countable as [g], Z_countable as [h].
exists (fun q:Q => match q with n # d => f (h n, g d) end)%Q.
intros [n1 d1] [n2 d2] ?.
apply H in H2.
injection H2 as H2.
f_equal; auto.
