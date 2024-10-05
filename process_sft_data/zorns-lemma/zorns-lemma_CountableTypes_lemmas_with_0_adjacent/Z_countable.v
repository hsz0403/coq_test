Require Export FiniteTypes Relation_Definitions ZArith QArith IndexedFamilies.
Require Import InfiniteTypes CSB DecidableDec FunctionalExtensionality ProofIrrelevance DependentTypeChoice ClassicalChoice Arith ArithRing.
Local Close Scope Q_scope.
Set Asymmetric Patterns.
Inductive CountableT (X : Type) : Prop := | intro_nat_injection (f : X -> nat) : injective f -> CountableT X.
Definition Countable {X : Type} (S : Ensemble X) : Prop := CountableT {x:X | In S x}.

Lemma Z_countable: CountableT Z.
Proof.
destruct countable_nat_product as [f], positive_countable as [g].
exists (fun n:Z => match n with | Z0 => f (0, 0) | Zpos p => f (1, g p) | Zneg p => f (2, g p) end).
intros [|p1|p1] [|p2|p2] H1; apply H in H1; discriminate H1 + trivial; injection H1 as H1; f_equal; auto.
