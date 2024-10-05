Require Export FiniteTypes Relation_Definitions ZArith QArith IndexedFamilies.
Require Import InfiniteTypes CSB DecidableDec FunctionalExtensionality ProofIrrelevance DependentTypeChoice ClassicalChoice Arith ArithRing.
Local Close Scope Q_scope.
Set Asymmetric Patterns.
Inductive CountableT (X : Type) : Prop := | intro_nat_injection (f : X -> nat) : injective f -> CountableT X.
Definition Countable {X : Type} (S : Ensemble X) : Prop := CountableT {x:X | In S x}.

Lemma countable_union: forall {X A:Type} (F:IndexedFamily A X), CountableT A -> (forall a:A, Countable (F a)) -> Countable (IndexedUnion F).
Proof.
intros.
destruct (choice_on_dependent_type (fun (a:A) (f:{x:X | In (F a) x} -> nat) => injective f)) as [choice_fun_inj].
-
intro.
destruct (H0 a).
now exists f.
-
destruct (choice (fun (x:{x:X | In (IndexedUnion F) x}) (a:A) => In (F a) (proj1_sig x))) as [choice_fun_a].
+
destruct x as [x [a]].
now exists a.
+
destruct countable_nat_product as [g], H as [h].
exists (fun x:{x:X | In (IndexedUnion F) x} => g (h (choice_fun_a x), choice_fun_inj _ (exist _ _ (H2 x)))).
intros x1 x2 H4.
apply H3 in H4.
injection H4 as H5 H6.
apply H in H5.
revert H6.
generalize (H2 x1), (H2 x2).
rewrite H5.
intros.
apply H1 in H6.
injection H6.
destruct x1, x2.
apply subset_eq_compat.
