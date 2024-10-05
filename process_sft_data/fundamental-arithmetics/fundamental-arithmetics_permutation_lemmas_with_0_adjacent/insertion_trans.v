Require Import Wf_nat.
Require Import missing.
Require Export List Permutation.
Inductive insertion (A:Set) : A -> list A -> list A -> Prop := head_insertion : forall (x:A)(l:list A),(insertion A x l (x::l)) |tail_insertion : forall (x y:A)(l l':list A),(insertion A x l l')->(insertion A x (y::l) (y::l')).
Inductive is_set (A:Set) : list A->Prop := nil_is_set : (is_set A nil) |cons_is_set : forall (x:A)(l:list A),(is_set A l)->~(In x l)->(is_set A (x::l)).
Inductive is_permutation (A:Set) : list A->list A->Prop := nil_is_permutation : (is_permutation A nil nil) |cons_is_permutation : forall (l l':list A),(is_permutation A l l')->forall (x:A)(l'':(list A)),(insertion A x l' l'')->(is_permutation A (x::l) l'').

Lemma insertion_trans : forall (A:Set)(l0 l1:list A)(x:A),(insertion A x l0 l1)->forall (l2:list A)(y:A),(insertion A y l1 l2)->exists l3:list A,(insertion A y l0 l3)/\(insertion A x l3 l2).
induction 1;intros.
inversion H.
exists (y::l);split;[apply head_insertion | apply tail_insertion;apply head_insertion].
exists l';split;[trivial | apply head_insertion].
inversion H0.
exists (y0::y::l);split;[apply head_insertion | apply tail_insertion;apply tail_insertion;trivial].
elim (IHinsertion l'0 y0 H5);intro l3;intro.
elim H6;intros.
exists (y::l3);split;[apply tail_insertion | apply tail_insertion];trivial.
