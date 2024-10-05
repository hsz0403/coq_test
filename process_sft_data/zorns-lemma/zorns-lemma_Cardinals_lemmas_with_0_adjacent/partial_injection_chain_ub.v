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

Lemma partial_injection_chain_ub: forall S:Ensemble partial_injection, chain partial_injection_ord S -> exists x:partial_injection, forall y:partial_injection, In S y -> partial_injection_ord y x.
Proof.
intros.
pose (ub_dom := [x:X | exists y:partial_injection, In S y /\ In (pi_dom y) x]).
assert (forall x:X, In ub_dom x -> { y:Y | exists z:partial_injection, In S z /\ exists i:In (pi_dom z) x, pi_func z x i = y }).
intros.
apply constructive_definite_description.
destruct H0.
destruct H0.
destruct H0.
exists (pi_func x0 x H1).
red; split.
exists x0.
split.
assumption.
exists H1.
reflexivity.
intros.
destruct H2.
destruct H2.
destruct H3.
pose proof (H x0 x1 H0 H2).
case H4.
intro.
rewrite <- H3.
apply pi_func_ext.
assumption.
intro.
rewrite <- H3.
symmetry.
apply pi_func_ext.
assumption.
assert (forall (x1 x2:X) (i1:In ub_dom x1) (i2:In ub_dom x2), proj1_sig (X0 x1 i1) = proj1_sig (X0 x2 i2) -> x1 = x2).
intros.
destruct X0 in H0.
destruct X0 in H0.
simpl in H0.
destruct H0.
destruct e.
destruct H0.
destruct H1.
destruct e0.
destruct H2.
destruct H3.
destruct H1.
case (H x0 x4 H0 H2).
intro.
assert (In (pi_dom x4) x1).
apply (pi_dom_inc _ _ H1).
assumption.
assert (pi_func x4 x1 H4 = pi_func x4 x2 x5).
rewrite H3.
symmetry.
apply pi_func_ext.
assumption.
apply pi_inj in H5.
assumption.
intro.
assert (In (pi_dom x0) x2).
apply (pi_dom_inc _ _ H1).
assumption.
assert (pi_func x0 x1 x3 = pi_func x0 x2 H4).
rewrite <- H3.
apply pi_func_ext.
assumption.
apply pi_inj in H5.
assumption.
exists (Build_partial_injection ub_dom (fun (x:X) (i:In ub_dom x) => proj1_sig (X0 x i)) H0).
intros.
constructor.
simpl.
red; intros.
constructor.
exists y.
tauto.
simpl.
intros.
destruct (X0 x i2).
simpl.
destruct e.
destruct H2.
destruct H3.
destruct H3.
case (H y x1 H1 H2).
intro.
apply pi_func_ext.
assumption.
intro.
symmetry.
apply pi_func_ext.
assumption.
