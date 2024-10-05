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

Lemma no_dup1 : forall (a : A) (l : list A), In a l -> In a (no_dup l).
Proof.
intros.
induction l as [| a0 l Hrecl].
elim H.
simpl in |- *.
induction H as [H| H].
induction (In_dec Aeq_dec a0 (no_dup l)).
rewrite <- H.
auto.
left.
auto.
induction (In_dec Aeq_dec a0 (no_dup l)).
auto.
right.
auto.
