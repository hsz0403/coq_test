Require Export FiniteTypes Relation_Definitions ZArith QArith IndexedFamilies.
Require Import InfiniteTypes CSB DecidableDec FunctionalExtensionality ProofIrrelevance DependentTypeChoice ClassicalChoice Arith ArithRing.
Local Close Scope Q_scope.
Set Asymmetric Patterns.
Inductive CountableT (X : Type) : Prop := | intro_nat_injection (f : X -> nat) : injective f -> CountableT X.
Definition Countable {X : Type} (S : Ensemble X) : Prop := CountableT {x:X | In S x}.

Lemma inj_countable {X Y : Type} (f : X -> Y) : CountableT Y -> injective f -> CountableT X.
Proof.
intros [g] ?.
exists (fun x:X => g (f x)).
intros x1 x2 ?.
auto.
