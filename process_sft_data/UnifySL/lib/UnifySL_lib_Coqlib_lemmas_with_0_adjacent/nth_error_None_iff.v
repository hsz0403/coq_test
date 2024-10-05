Require Import Coq.Sets.Ensembles.
Require Import Coq.Lists.List.
Require Import Coq.omega.Omega.
Require Import Coq.Logic.ClassicalFacts.
Inductive remove_rel {A: Type}: A -> list A -> list A -> Prop := | remove_rel_nil: forall a, remove_rel a nil nil | remove_rel_cons_eq: forall a xs ys, remove_rel a xs ys -> remove_rel a (a :: xs) ys | remove_rel_cons_neq: forall a b xs ys, a <> b -> remove_rel a xs ys -> remove_rel a (b :: xs) (b :: ys).
Definition isSome {A} (o: option A) := match o with Some _ => True | None => False end.

Lemma nth_error_None_iff: forall {A} (l: list A) n, nth_error l n = None <-> n >= length l.
Proof.
intros.
revert n; induction l; intros; destruct n; simpl.
+
split; [intros _; omega | auto].
+
split; [intros _; omega | auto].
+
split; [intros; inversion H | omega].
+
rewrite IHl.
omega.
