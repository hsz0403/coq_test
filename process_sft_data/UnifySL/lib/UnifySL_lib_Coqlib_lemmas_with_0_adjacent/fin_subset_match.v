Require Import Coq.Sets.Ensembles.
Require Import Coq.Lists.List.
Require Import Coq.omega.Omega.
Require Import Coq.Logic.ClassicalFacts.
Inductive remove_rel {A: Type}: A -> list A -> list A -> Prop := | remove_rel_nil: forall a, remove_rel a nil nil | remove_rel_cons_eq: forall a xs ys, remove_rel a xs ys -> remove_rel a (a :: xs) ys | remove_rel_cons_neq: forall a b xs ys, a <> b -> remove_rel a xs ys -> remove_rel a (b :: xs) (b :: ys).
Definition isSome {A} (o: option A) := match o with Some _ => True | None => False end.

Lemma fin_subset_match {A B: Type} {P: A -> B -> Prop}: forall (X: Ensemble A) (Y: Ensemble B), (forall x, X x -> exists y, P x y /\ Y y) -> forall xs, Forall (fun x => X x) xs -> exists ys, Forall2 P xs ys /\ Forall (fun y => Y y) ys.
Proof.
intros.
induction xs as [| x0 xs].
+
exists nil; split; constructor.
+
inversion H0; subst.
specialize (IHxs H4).
destruct IHxs as [ys [? ?]].
specialize (H x0 H3).
destruct H as [y0 [? ?]].
exists (y0 :: ys).
split; constructor; auto.
