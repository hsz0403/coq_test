Require Export FunctionProperties.
Require Export Relation_Definitions.
Require Import Relation_Definitions_Implicit.
Require Import CSB.
Require Import EnsemblesSpec.
Inductive Cardinal : Type := | cardinality: Type -> Cardinal.
Fixpoint n_element_set (n:nat) : Set := match n with | O => False | S m => option (n_element_set m) end.
Definition nat_to_cardinal (n:nat) := cardinality (n_element_set n).
Definition aleph0 := cardinality nat.
Inductive eq_cardinal : Cardinal -> Cardinal -> Prop := | bij_eq_cardinal: forall {X Y:Type} (f:X->Y), bijective f -> eq_cardinal (cardinality X) (cardinality Y).
Inductive le_cardinal : Cardinal -> Cardinal -> Prop := | inj_le_cardinal: forall {X Y:Type} (f:X->Y), injective f -> le_cardinal (cardinality X) (cardinality Y).
Definition lt_cardinal (kappa lambda:Cardinal) : Prop := le_cardinal kappa lambda /\ ~ eq_cardinal kappa lambda.
Definition ge_cardinal (kappa lambda:Cardinal) : Prop := le_cardinal lambda kappa.
Definition gt_cardinal (kappa lambda:Cardinal) : Prop := lt_cardinal lambda kappa.
Require Import ClassicalChoice.
Require Import ZornsLemma.
Require Import EnsemblesImplicit.
Require Import ProofIrrelevance.
Require Import FunctionalExtensionality.
Require Import Description.
Section le_cardinal_total.
Variable X Y:Type.
Record partial_injection : Type := { pi_dom: Ensemble X; pi_func: forall x:X, In pi_dom x -> Y; pi_inj: forall (x1 x2:X) (i1:In pi_dom x1) (i2:In pi_dom x2), pi_func x1 i1 = pi_func x2 i2 -> x1 = x2 }.
Record partial_injection_ord (pi1 pi2:partial_injection) : Prop := { pi_dom_inc: Included (pi_dom pi1) (pi_dom pi2); pi_func_ext: forall (x:X) (i1:In (pi_dom pi1) x) (i2:In (pi_dom pi2) x), pi_func pi1 x i1 = pi_func pi2 x i2 }.
End le_cardinal_total.

Lemma premaximal_pi_is_full_or_surj: forall x:partial_injection, premaximal partial_injection_ord x -> pi_dom x = Full_set \/ forall y:Y, exists x0:X, exists i:(In (pi_dom x) x0), pi_func x x0 i = y.
Proof.
intros.
case (classic (pi_dom x = Full_set)).
left.
trivial.
intro.
assert (exists x0:X, ~ In (pi_dom x) x0).
apply NNPP.
intuition.
apply H0.
apply Extensionality_Ensembles.
red; split.
red; intros.
constructor.
red; intros.
apply NNPP.
intuition.
apply H1.
exists x0.
assumption.
right.
destruct H1.
intros.
apply NNPP.
intuition.
pose (pi_dom_ext := Add (pi_dom x) x0).
assert (forall (x':X), In pi_dom_ext x' -> { y':Y | (exists i2:In (pi_dom x) x', y' = pi_func x x' i2) \/ (x' = x0 /\ y' = y) }).
intros.
apply constructive_definite_description.
case H3.
intros.
exists (pi_func x x1 H4).
red; split.
left.
exists H4.
reflexivity.
intros.
case H5.
intro.
destruct H6.
rewrite H6.
assert (H4 = x2).
apply proof_irrelevance.
rewrite H7.
reflexivity.
intros.
destruct H6.
contradict H1.
rewrite <- H6.
assumption.
intros.
destruct H4.
exists y.
red; split.
right.
tauto.
intros.
case H4.
intro.
destruct H5.
contradiction H1.
intros.
symmetry.
tauto.
pose (pi_func_ext0 := fun (x:X) (i:In pi_dom_ext x) => proj1_sig (X0 x i)).
assert (forall (x1:X) (i:In (pi_dom x) x1) (i2:In pi_dom_ext x1), pi_func_ext0 x1 i2 = pi_func x x1 i).
intros.
unfold pi_func_ext0.
destruct (X0 x1 i2).
simpl.
case o.
intros.
destruct H3.
assert (i = x3).
apply proof_irrelevance.
rewrite H4.
assumption.
intros.
destruct H3.
contradiction H1.
rewrite <- H3.
assumption.
assert (forall (i:In pi_dom_ext x0), pi_func_ext0 x0 i = y).
intros.
unfold pi_func_ext0.
destruct (X0 x0 i); simpl.
case o.
intro.
destruct H4.
contradiction H1.
tauto.
assert (forall (x1 x2:X) (i1:In pi_dom_ext x1) (i2:In pi_dom_ext x2), pi_func_ext0 x1 i1 = pi_func_ext0 x2 i2 -> x1 = x2).
intros.
inversion i1.
inversion i2.
rewrite (H3 x1 H6 i1) in H5.
rewrite (H3 x2 H8 i2) in H5.
apply pi_inj in H5.
assumption.
destruct H8.
rewrite (H3 x1 H6 i1) in H5.
rewrite H4 in H5.
contradiction H2.
exists x1.
exists H6.
assumption.
destruct H6.
rewrite H4 in H5.
inversion i2.
rewrite (H3 x2 H6 i2) in H5.
contradiction H2.
exists x2.
exists H6.
symmetry; assumption.
destruct H6.
reflexivity.
pose (pi_ext := Build_partial_injection pi_dom_ext pi_func_ext0 H5).
assert (partial_injection_ord x pi_ext).
constructor.
unfold pi_ext; simpl.
unfold pi_dom_ext.
red; intros.
left.
assumption.
intros.
symmetry.
apply H3.
apply H in H6.
contradiction H1.
apply (pi_dom_inc _ _ H6).
simpl.
right.
auto with sets.
