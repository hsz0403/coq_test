Require Import Wf_nat.
Require Import missing.
Require Export List Permutation.
Inductive insertion (A:Set) : A -> list A -> list A -> Prop := head_insertion : forall (x:A)(l:list A),(insertion A x l (x::l)) |tail_insertion : forall (x y:A)(l l':list A),(insertion A x l l')->(insertion A x (y::l) (y::l')).
Inductive is_set (A:Set) : list A->Prop := nil_is_set : (is_set A nil) |cons_is_set : forall (x:A)(l:list A),(is_set A l)->~(In x l)->(is_set A (x::l)).
Inductive is_permutation (A:Set) : list A->list A->Prop := nil_is_permutation : (is_permutation A nil nil) |cons_is_permutation : forall (l l':list A),(is_permutation A l l')->forall (x:A)(l'':(list A)),(insertion A x l' l'')->(is_permutation A (x::l) l'').

Lemma is_set_insertion_in : forall (A:Set)(l l':list A)(x:A),(insertion A x l l')->(is_set A l')->~(In x l).
induction l;simpl;try tauto;intros.
inversion H;rewrite <- H3 in H0;inversion H0.
simpl in H7;trivial.
intro.
case H10;intro.
apply H9;rewrite H11;eapply insertion_in;apply H5.
elim (IHl l'0 x H5 H8 H11).
