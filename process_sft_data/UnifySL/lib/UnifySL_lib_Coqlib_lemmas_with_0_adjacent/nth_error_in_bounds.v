Require Import Coq.Sets.Ensembles.
Require Import Coq.Lists.List.
Require Import Coq.omega.Omega.
Require Import Coq.Logic.ClassicalFacts.
Inductive remove_rel {A: Type}: A -> list A -> list A -> Prop := | remove_rel_nil: forall a, remove_rel a nil nil | remove_rel_cons_eq: forall a xs ys, remove_rel a xs ys -> remove_rel a (a :: xs) ys | remove_rel_cons_neq: forall a b xs ys, a <> b -> remove_rel a xs ys -> remove_rel a (b :: xs) (b :: ys).
Definition isSome {A} (o: option A) := match o with Some _ => True | None => False end.

Lemma nth_error_in_bounds: forall {A} (l: list A) i, (O <= i < length l)%nat -> exists x, nth_error l i = value x.
Proof.
intros until i; intros H.
revert i l H.
induction i; destruct l; intros; simpl in *; try solve [eauto | omega].
apply IHi; omega.
