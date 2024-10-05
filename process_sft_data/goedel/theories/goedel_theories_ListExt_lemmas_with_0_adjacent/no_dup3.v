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

Lemma no_dup3 : forall (k l : list A) (a : A), no_dup k = a :: l -> ~ In a l.
Proof.
intro.
induction k as [| a k Hreck].
intros.
discriminate H.
unfold not in |- *; intros.
simpl in H.
induction (In_dec Aeq_dec a (no_dup k)).
elim Hreck with l a0; auto.
elim b.
inversion H.
rewrite H3.
auto.
