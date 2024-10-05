Require Export Ensembles.
Require Import EnsemblesImplicit.
Require Export Image.
Require Import ImageImplicit.
Require Export Finite_sets.
Require Export FunctionProperties.
Require Import DecidableDec.
Require Import ProofIrrelevance.
Require Import Description.
Set Asymmetric Patterns.
Inductive FiniteT : Type -> Prop := | empty_finite: FiniteT False | add_finite: forall T:Type, FiniteT T -> FiniteT (option T) | bij_finite: forall (X Y:Type) (f:X->Y), FiniteT X -> invertible f -> FiniteT Y.
Require Import FunctionalExtensionality.
Definition FiniteT_nat_cardinal (X:Type) (H:FiniteT X) : nat := proj1_sig (constructive_definite_description _ (FiniteT_has_nat_cardinal X H)).

Lemma Finite_ens_type: forall {X:Type} (S:Ensemble X), Finite _ S -> FiniteT { x:X | In S x }.
Proof.
intros.
induction H.
apply bij_finite with False (False_rect _).
constructor.
assert (g:{x:X | In Empty_set x}->False).
intro.
destruct X0.
destruct i.
exists g.
destruct x.
destruct y.
destruct g.
assert (Included A (Add A x)).
auto with sets.
assert (In (Add A x) x).
auto with sets.
pose (g := fun (y: option {x:X | In A x}) => match y return {x0:X | In (Add A x) x0} with | Some (exist y0 i) => exist (fun x2:X => In (Add A x) x2) y0 (H1 y0 i) | None => exist (fun x2:X => In (Add A x) x2) x H2 end).
apply bij_finite with _ g.
apply add_finite.
assumption.
assert (h:forall x0:X, In (Add A x) x0 -> { In A x0 } + { x0 = x }).
intros; apply exclusive_dec.
intuition.
destruct H6; auto.
destruct H3.
left; assumption.
right; destruct H3; reflexivity.
pose (ginv := fun s:{x0:X | In (Add A x) x0} => match s return option {x:X | In A x} with | exist x0 i => match (h x0 i) with | left iA => Some (exist _ x0 iA) | right _ => None end end).
exists ginv.
intro; destruct x0.
destruct s.
simpl.
remember (h x0 (H1 x0 i)) as sum; destruct sum.
destruct (proof_irrelevance _ i i0).
reflexivity.
contradiction H0.
rewrite <- e; assumption.
simpl.
remember (h x H2) as sum; destruct sum.
contradiction H0.
reflexivity.
intro.
unfold ginv.
destruct y.
destruct (h x0 i).
simpl.
generalize (H1 x0 i0); intro.
destruct (proof_irrelevance _ i i1).
reflexivity.
simpl.
destruct e.
destruct (proof_irrelevance _ H2 i).
reflexivity.
