Require Import Wf_nat.
Require Import missing.
Require Export List Permutation.
Inductive insertion (A:Set) : A -> list A -> list A -> Prop := head_insertion : forall (x:A)(l:list A),(insertion A x l (x::l)) |tail_insertion : forall (x y:A)(l l':list A),(insertion A x l l')->(insertion A x (y::l) (y::l')).
Inductive is_set (A:Set) : list A->Prop := nil_is_set : (is_set A nil) |cons_is_set : forall (x:A)(l:list A),(is_set A l)->~(In x l)->(is_set A (x::l)).
Inductive is_permutation (A:Set) : list A->list A->Prop := nil_is_permutation : (is_permutation A nil nil) |cons_is_permutation : forall (l l':list A),(is_permutation A l l')->forall (x:A)(l'':(list A)),(insertion A x l' l'')->(is_permutation A (x::l) l'').

Lemma is_permutation_set : forall (A:Set)(l l':list A),(is_permutation _ l l')->(is_set _ l)->(is_set _ l').
induction 1.
auto.
intros.
inversion H1.
subst x0;subst l0.
eapply insertion_is_set.
apply IHis_permutation.
auto.
elim (permutation_in _ _ _ H x).
intros.
red;intro.
apply H5.
apply H3.
apply H6.
auto.
