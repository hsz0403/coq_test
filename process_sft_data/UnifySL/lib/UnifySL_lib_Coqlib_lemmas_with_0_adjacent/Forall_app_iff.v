Require Import Coq.Sets.Ensembles.
Require Import Coq.Lists.List.
Require Import Coq.omega.Omega.
Require Import Coq.Logic.ClassicalFacts.
Inductive remove_rel {A: Type}: A -> list A -> list A -> Prop := | remove_rel_nil: forall a, remove_rel a nil nil | remove_rel_cons_eq: forall a xs ys, remove_rel a xs ys -> remove_rel a (a :: xs) ys | remove_rel_cons_neq: forall a b xs ys, a <> b -> remove_rel a xs ys -> remove_rel a (b :: xs) (b :: ys).
Definition isSome {A} (o: option A) := match o with Some _ => True | None => False end.

Lemma Forall_app_iff: forall {A : Type} (P : A -> Prop) (l1 l2 : list A), Forall P (l1 ++ l2) <-> Forall P l1 /\ Forall P l2.
Proof.
intros; induction l1; intros.
+
simpl.
assert (Forall P nil) by constructor; tauto.
+
simpl; split; intros.
-
inversion H; subst; split; try tauto.
constructor; auto; tauto.
-
destruct H.
inversion H; subst.
constructor; auto; tauto.
