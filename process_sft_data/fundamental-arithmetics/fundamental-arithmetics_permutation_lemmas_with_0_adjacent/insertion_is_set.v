Require Import Wf_nat.
Require Import missing.
Require Export List Permutation.
Inductive insertion (A:Set) : A -> list A -> list A -> Prop := head_insertion : forall (x:A)(l:list A),(insertion A x l (x::l)) |tail_insertion : forall (x y:A)(l l':list A),(insertion A x l l')->(insertion A x (y::l) (y::l')).
Inductive is_set (A:Set) : list A->Prop := nil_is_set : (is_set A nil) |cons_is_set : forall (x:A)(l:list A),(is_set A l)->~(In x l)->(is_set A (x::l)).
Inductive is_permutation (A:Set) : list A->list A->Prop := nil_is_permutation : (is_permutation A nil nil) |cons_is_permutation : forall (l l':list A),(is_permutation A l l')->forall (x:A)(l'':(list A)),(insertion A x l' l'')->(is_permutation A (x::l) l'').

Lemma insertion_is_set : forall (A:Set)(l:list A),(is_set _ l)->forall (x:A),~(In x l)->forall (l':list A),(insertion _ x l l')->(is_set _ l').
induction 1.
intros.
inversion H0.
apply cons_is_set.
apply nil_is_set.
auto.
intros.
inversion H2.
subst x1.
subst l0.
subst l'.
apply cons_is_set.
eapply IHis_set.
apply H0.
apply head_insertion.
auto.
subst x1;subst y;subst l0.
apply cons_is_set.
eapply IHis_set with x0;auto.
red;intro.
apply H1.
simpl.
right;auto.
red;intro.
case (in_insertion_inv _ _ _ _ _ H7 H3);intro.
apply H1.
simpl.
left;auto.
apply H0.
auto.
