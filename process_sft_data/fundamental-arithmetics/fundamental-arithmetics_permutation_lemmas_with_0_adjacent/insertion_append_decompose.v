Require Import Wf_nat.
Require Import missing.
Require Export List Permutation.
Inductive insertion (A:Set) : A -> list A -> list A -> Prop := head_insertion : forall (x:A)(l:list A),(insertion A x l (x::l)) |tail_insertion : forall (x y:A)(l l':list A),(insertion A x l l')->(insertion A x (y::l) (y::l')).
Inductive is_set (A:Set) : list A->Prop := nil_is_set : (is_set A nil) |cons_is_set : forall (x:A)(l:list A),(is_set A l)->~(In x l)->(is_set A (x::l)).
Inductive is_permutation (A:Set) : list A->list A->Prop := nil_is_permutation : (is_permutation A nil nil) |cons_is_permutation : forall (l l':list A),(is_permutation A l l')->forall (x:A)(l'':(list A)),(insertion A x l' l'')->(is_permutation A (x::l) l'').

Lemma insertion_append_decompose : forall (A:Set)(x:A)(l l':list A),(insertion _ x l l')->exists l1:list A,exists l2:list A,l=(app l1 l2)/\l'=(app l1 (cons x l2)).
induction 1.
exists (nil (A:=A)).
exists l.
split;try reflexivity.
elim IHinsertion.
intro l1.
intro.
elim H0.
intro l2;intros.
elim H1;clear H1;intros.
exists (cons y l1).
exists l2.
subst l;subst l'.
split;try reflexivity.
