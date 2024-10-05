Require Export FiniteTypes Relation_Definitions ZArith QArith IndexedFamilies.
Require Import InfiniteTypes CSB DecidableDec FunctionalExtensionality ProofIrrelevance DependentTypeChoice ClassicalChoice Arith ArithRing.
Local Close Scope Q_scope.
Set Asymmetric Patterns.
Inductive CountableT (X : Type) : Prop := | intro_nat_injection (f : X -> nat) : injective f -> CountableT X.
Definition Countable {X : Type} (S : Ensemble X) : Prop := CountableT {x:X | In S x}.

Lemma countable_img {X Y : Type} (f : X -> Y) (S : Ensemble X) : Countable S -> Countable (Im S f).
Proof.
intros.
assert (forall x, In S x -> In (Im S f) (f x)) by auto with sets.
pose (fS := fun x => match x with | exist x0 i => exist _ (f x0) (H0 x0 i) end).
apply surj_countable with fS; trivial.
intros [? [x i y e]].
exists (exist _ x i).
simpl.
generalize (H0 x i); intro.
generalize (Im_intro X Y S f x i y e); intro.
now destruct e, (proof_irrelevance _ i0 i1).
