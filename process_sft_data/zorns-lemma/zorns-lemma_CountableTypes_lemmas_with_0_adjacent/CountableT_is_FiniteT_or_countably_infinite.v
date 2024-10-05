Require Export FiniteTypes Relation_Definitions ZArith QArith IndexedFamilies.
Require Import InfiniteTypes CSB DecidableDec FunctionalExtensionality ProofIrrelevance DependentTypeChoice ClassicalChoice Arith ArithRing.
Local Close Scope Q_scope.
Set Asymmetric Patterns.
Inductive CountableT (X : Type) : Prop := | intro_nat_injection (f : X -> nat) : injective f -> CountableT X.
Definition Countable {X : Type} (S : Ensemble X) : Prop := CountableT {x:X | In S x}.

Lemma CountableT_is_FiniteT_or_countably_infinite (X : Type) : CountableT X -> {FiniteT X} + {exists f : X -> nat, bijective f}.
Proof.
intros.
apply exclusive_dec.
-
intro.
destruct H0 as [? [f ?]].
contradiction nat_infinite.
apply bij_finite with _ f; trivial.
apply bijective_impl_invertible; trivial.
-
destruct (classic (FiniteT X)).
+
left; trivial.
+
right.
apply infinite_nat_inj in H0.
destruct H, H0 as [g].
now apply CSB with f g.
