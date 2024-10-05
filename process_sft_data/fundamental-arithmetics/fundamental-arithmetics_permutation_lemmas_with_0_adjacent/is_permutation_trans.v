Require Import Wf_nat.
Require Import missing.
Require Export List Permutation.
Inductive insertion (A:Set) : A -> list A -> list A -> Prop := head_insertion : forall (x:A)(l:list A),(insertion A x l (x::l)) |tail_insertion : forall (x y:A)(l l':list A),(insertion A x l l')->(insertion A x (y::l) (y::l')).
Inductive is_set (A:Set) : list A->Prop := nil_is_set : (is_set A nil) |cons_is_set : forall (x:A)(l:list A),(is_set A l)->~(In x l)->(is_set A (x::l)).
Inductive is_permutation (A:Set) : list A->list A->Prop := nil_is_permutation : (is_permutation A nil nil) |cons_is_permutation : forall (l l':list A),(is_permutation A l l')->forall (x:A)(l'':(list A)),(insertion A x l' l'')->(is_permutation A (x::l) l'').

Lemma is_permutation_trans : forall (A:Set)(l l':list A),(is_permutation A l l')->forall (l'':list A),(is_permutation A l' l'')->(is_permutation A l l'').
induction l.
intros.
inversion H.
rewrite <- H2 in H0;trivial.
intros.
inversion H.
induction H5;inversion H0.
eapply cons_is_permutation;try (apply IHl with l1;eauto);trivial.
eapply permutation_insertion_permutation.
apply H3.
apply tail_insertion.
apply H5.
eapply cons_is_permutation.
apply H8.
apply H10.
