Require Export FiniteTypes Relation_Definitions ZArith QArith IndexedFamilies.
Require Import InfiniteTypes CSB DecidableDec FunctionalExtensionality ProofIrrelevance DependentTypeChoice ClassicalChoice Arith ArithRing.
Local Close Scope Q_scope.
Set Asymmetric Patterns.
Inductive CountableT (X : Type) : Prop := | intro_nat_injection (f : X -> nat) : injective f -> CountableT X.
Definition Countable {X : Type} (S : Ensemble X) : Prop := CountableT {x:X | In S x}.

Lemma FiniteT_impl_CountableT (X : Type) : FiniteT X -> CountableT X.
Proof.
intros.
induction H.
-
exists (False_rect nat).
now intro.
-
destruct IHFiniteT.
exists (fun x => match x with | Some x0 => S (f x0) | None => 0 end).
intros [x1|] [x2|] H1; injection H1 as H1 + discriminate H1 + trivial.
now destruct (H0 _ _ H1).
-
destruct IHFiniteT as [g], H0 as [finv].
exists (fun y:Y => g (finv y)).
intros y1 y2 ?.
apply H1 in H3.
congruence.
