Require Import Wf_nat.
Require Import missing.
Require Export List Permutation.
Inductive insertion (A:Set) : A -> list A -> list A -> Prop := head_insertion : forall (x:A)(l:list A),(insertion A x l (x::l)) |tail_insertion : forall (x y:A)(l l':list A),(insertion A x l l')->(insertion A x (y::l) (y::l')).
Inductive is_set (A:Set) : list A->Prop := nil_is_set : (is_set A nil) |cons_is_set : forall (x:A)(l:list A),(is_set A l)->~(In x l)->(is_set A (x::l)).
Inductive is_permutation (A:Set) : list A->list A->Prop := nil_is_permutation : (is_permutation A nil nil) |cons_is_permutation : forall (l l':list A),(is_permutation A l l')->forall (x:A)(l'':(list A)),(insertion A x l' l'')->(is_permutation A (x::l) l'').

Lemma permutation_insertion : forall (A:Set)(l0 l1:list A),(is_permutation A l0 l1)->forall (x:A)(l2 l3:list A),(insertion A x l0 l2)->(insertion A x l1 l3)->(is_permutation A l2 l3).
induction 1;intros.
inversion H;inversion H0;apply is_permutation_refl.
inversion H1.
apply cons_is_permutation with l'';trivial.
apply cons_is_permutation with l';trivial.
elim (insertion_trans A l' l'' x H0 l3 x0 H2).
intro l4;intro.
elim H8;intros.
apply cons_is_permutation with l4;trivial.
eapply IHis_permutation;eauto.
