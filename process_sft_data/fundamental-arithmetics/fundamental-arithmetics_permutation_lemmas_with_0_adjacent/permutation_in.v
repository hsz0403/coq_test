Require Import Wf_nat.
Require Import missing.
Require Export List Permutation.
Inductive insertion (A:Set) : A -> list A -> list A -> Prop := head_insertion : forall (x:A)(l:list A),(insertion A x l (x::l)) |tail_insertion : forall (x y:A)(l l':list A),(insertion A x l l')->(insertion A x (y::l) (y::l')).
Inductive is_set (A:Set) : list A->Prop := nil_is_set : (is_set A nil) |cons_is_set : forall (x:A)(l:list A),(is_set A l)->~(In x l)->(is_set A (x::l)).
Inductive is_permutation (A:Set) : list A->list A->Prop := nil_is_permutation : (is_permutation A nil nil) |cons_is_permutation : forall (l l':list A),(is_permutation A l l')->forall (x:A)(l'':(list A)),(insertion A x l' l'')->(is_permutation A (x::l) l'').

Lemma permutation_in : forall (A:Set)(l l':list A),(is_permutation A l l')->forall (x:A),(In x l)<->(In x l').
induction l;simpl;intros.
inversion H;simpl;tauto.
inversion H;simpl.
split;intro.
case H5;intro.
eapply insertion_in;rewrite H6 in H4;apply H4.
elim (IHl l'0 H2 x);intros.
eapply insertion_inclusion;eauto.
case (in_insertion_inv A x a l'0 l' H4 H5);intro.
rewrite H6;tauto.
elim (IHl l'0 H2 x);intros.
right;auto.
