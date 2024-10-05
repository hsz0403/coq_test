Require Export FiniteTypes Relation_Definitions ZArith QArith IndexedFamilies.
Require Import InfiniteTypes CSB DecidableDec FunctionalExtensionality ProofIrrelevance DependentTypeChoice ClassicalChoice Arith ArithRing.
Local Close Scope Q_scope.
Set Asymmetric Patterns.
Inductive CountableT (X : Type) : Prop := | intro_nat_injection (f : X -> nat) : injective f -> CountableT X.
Definition Countable {X : Type} (S : Ensemble X) : Prop := CountableT {x:X | In S x}.

Lemma countable_downward_closed {X : Type} (S T : Ensemble X) : Countable T -> Included S T -> Countable S.
Proof.
intros [f H] H0.
exists (fun x => match x with | exist x0 i => f (exist _ x0 (H0 _ i)) end).
intros [x1] [x2] H1.
apply H in H1.
injection H1 as H1.
now destruct H1, (proof_irrelevance _ i i0).
