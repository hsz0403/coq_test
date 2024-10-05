Require Export FiniteTypes Relation_Definitions ZArith QArith IndexedFamilies.
Require Import InfiniteTypes CSB DecidableDec FunctionalExtensionality ProofIrrelevance DependentTypeChoice ClassicalChoice Arith ArithRing.
Local Close Scope Q_scope.
Set Asymmetric Patterns.
Inductive CountableT (X : Type) : Prop := | intro_nat_injection (f : X -> nat) : injective f -> CountableT X.
Definition Countable {X : Type} (S : Ensemble X) : Prop := CountableT {x:X | In S x}.

Lemma countable_sum (X Y : Type) : CountableT X -> CountableT Y -> CountableT (X + Y).
Proof.
intros [f] [g].
destruct countable_nat_product as [h].
exists (fun s:X+Y => match s with | inl x => h (0, f x) | inr y => h (1, g y) end).
intros [x1|y1] [x2|y2] ?; apply H1 in H2; try discriminate H2; intros; f_equal; apply H + apply H0; now injection H2.
