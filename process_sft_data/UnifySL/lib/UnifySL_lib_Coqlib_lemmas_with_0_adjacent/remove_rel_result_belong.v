Require Import Coq.Sets.Ensembles.
Require Import Coq.Lists.List.
Require Import Coq.omega.Omega.
Require Import Coq.Logic.ClassicalFacts.
Inductive remove_rel {A: Type}: A -> list A -> list A -> Prop := | remove_rel_nil: forall a, remove_rel a nil nil | remove_rel_cons_eq: forall a xs ys, remove_rel a xs ys -> remove_rel a (a :: xs) ys | remove_rel_cons_neq: forall a b xs ys, a <> b -> remove_rel a xs ys -> remove_rel a (b :: xs) (b :: ys).
Definition isSome {A} (o: option A) := match o with Some _ => True | None => False end.

Lemma remove_rel_result_belong: forall (A : Type) (l1 l2 : list A) (x : A), remove_rel x l1 l2 -> Forall (fun y => In y l1) l2.
Proof.
intros.
induction H.
+
auto.
+
simpl.
revert IHremove_rel; apply Forall_impl.
intros; auto.
+
constructor; simpl; auto.
revert IHremove_rel; apply Forall_impl.
intros; auto.
