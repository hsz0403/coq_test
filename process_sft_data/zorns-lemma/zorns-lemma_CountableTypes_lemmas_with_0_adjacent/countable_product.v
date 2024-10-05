Require Export FiniteTypes Relation_Definitions ZArith QArith IndexedFamilies.
Require Import InfiniteTypes CSB DecidableDec FunctionalExtensionality ProofIrrelevance DependentTypeChoice ClassicalChoice Arith ArithRing.
Local Close Scope Q_scope.
Set Asymmetric Patterns.
Inductive CountableT (X : Type) : Prop := | intro_nat_injection (f : X -> nat) : injective f -> CountableT X.
Definition Countable {X : Type} (S : Ensemble X) : Prop := CountableT {x:X | In S x}.

Lemma countable_product (X Y:Type) : CountableT X -> CountableT Y -> CountableT (X * Y).
Proof.
intros [f] [g].
pose (fg := fun (p:X*Y) => let (x,y):=p in (f x, g y)).
destruct countable_nat_product as [h].
exists (fun p:X*Y => h (fg p)).
intros [x1 y1] [x2 y2] H2.
apply H1 in H2.
injection H2 as H3 H4.
apply H in H3.
apply H0 in H4.
now subst.
