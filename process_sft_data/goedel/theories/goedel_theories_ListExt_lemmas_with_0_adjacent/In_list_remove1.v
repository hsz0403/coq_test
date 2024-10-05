Require Import Coq.Lists.List.
Section List_Remove.
Variable A : Set.
Hypothesis Aeq_dec : forall a b : A, {a = b} + {a <> b}.
Definition list_remove (x : A) (l : list A) : list A := list_rec (fun _ => list A) nil (fun (a : A) _ (recl : list A) => match Aeq_dec a x with | left _ => recl | right _ => a :: recl end) l.
End List_Remove.
Section No_Duplicate.
Variable A : Set.
Hypothesis Aeq_dec : forall a b : A, {a = b} + {a <> b}.
Definition no_dup (l : list A) : list A := list_rec (fun _ => list A) nil (fun (a : A) _ (rec : list A) => match In_dec Aeq_dec a rec with | left _ => rec | right _ => a :: rec end) l.
End No_Duplicate.

Lemma In_list_remove1 : forall (a b : A) (l : list A), In a (list_remove b l) -> In a l.
Proof.
intros.
induction l as [| a0 l Hrecl].
elim H.
simpl in H.
induction (Aeq_dec a0 b).
right.
auto.
induction H as [H| H].
simpl in |- *; auto.
right.
auto.
