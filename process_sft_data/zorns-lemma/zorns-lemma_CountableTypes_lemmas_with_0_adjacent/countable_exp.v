Require Export FiniteTypes Relation_Definitions ZArith QArith IndexedFamilies.
Require Import InfiniteTypes CSB DecidableDec FunctionalExtensionality ProofIrrelevance DependentTypeChoice ClassicalChoice Arith ArithRing.
Local Close Scope Q_scope.
Set Asymmetric Patterns.
Inductive CountableT (X : Type) : Prop := | intro_nat_injection (f : X -> nat) : injective f -> CountableT X.
Definition Countable {X : Type} (S : Ensemble X) : Prop := CountableT {x:X | In S x}.

Lemma countable_exp (X Y : Type) : FiniteT X -> CountableT Y -> CountableT (X -> Y).
Proof.
intros.
induction H.
-
exists (fun _ => 0).
red; intros.
extensionality f.
destruct f.
-
destruct (countable_product (T -> Y) Y); trivial.
exists (fun g => f (fun x => g (Some x), g None)).
intros g1 g2 ?.
apply H1 in H2.
extensionality o.
destruct o; injection H2; trivial.
intros.
pose proof (equal_f H4).
apply H5.
-
destruct H1, IHFiniteT.
exists (fun h => f0 (fun x => h (f x))).
intros h1 h2 ?.
apply H3 in H4.
pose proof (equal_f H4).
simpl in H5.
extensionality y.
rewrite <- (H2 y).
apply H5.
