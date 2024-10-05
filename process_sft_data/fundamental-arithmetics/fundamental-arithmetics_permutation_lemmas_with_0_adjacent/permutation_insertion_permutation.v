Require Import Wf_nat.
Require Import missing.
Require Export List Permutation.
Inductive insertion (A:Set) : A -> list A -> list A -> Prop := head_insertion : forall (x:A)(l:list A),(insertion A x l (x::l)) |tail_insertion : forall (x y:A)(l l':list A),(insertion A x l l')->(insertion A x (y::l) (y::l')).
Inductive is_set (A:Set) : list A->Prop := nil_is_set : (is_set A nil) |cons_is_set : forall (x:A)(l:list A),(is_set A l)->~(In x l)->(is_set A (x::l)).
Inductive is_permutation (A:Set) : list A->list A->Prop := nil_is_permutation : (is_permutation A nil nil) |cons_is_permutation : forall (l l':list A),(is_permutation A l l')->forall (x:A)(l'':(list A)),(insertion A x l' l'')->(is_permutation A (x::l) l'').

Lemma permutation_insertion_permutation : forall (A:Set)(l l':list A),(is_permutation A l l')->forall (x:A)(l'':list A),(insertion A x l' l'')->forall (l''':list A),(is_permutation A l'' l''')->(is_permutation A (x::l) l''').
induction 1;intros.
inversion H.
rewrite <- H3 in H0.
trivial.
elim (permutation_insertion_comm A l'' l''0 x0 H1 l''' H2).
intro l1;intro.
elim H3;clear H3;intros.
eapply cons_is_permutation.
eapply IHis_permutation.
apply H0.
apply H3.
trivial.
