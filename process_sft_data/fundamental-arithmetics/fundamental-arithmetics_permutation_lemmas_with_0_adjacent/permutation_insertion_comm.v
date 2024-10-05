Require Import Wf_nat.
Require Import missing.
Require Export List Permutation.
Inductive insertion (A:Set) : A -> list A -> list A -> Prop := head_insertion : forall (x:A)(l:list A),(insertion A x l (x::l)) |tail_insertion : forall (x y:A)(l l':list A),(insertion A x l l')->(insertion A x (y::l) (y::l')).
Inductive is_set (A:Set) : list A->Prop := nil_is_set : (is_set A nil) |cons_is_set : forall (x:A)(l:list A),(is_set A l)->~(In x l)->(is_set A (x::l)).
Inductive is_permutation (A:Set) : list A->list A->Prop := nil_is_permutation : (is_permutation A nil nil) |cons_is_permutation : forall (l l':list A),(is_permutation A l l')->forall (x:A)(l'':(list A)),(insertion A x l' l'')->(is_permutation A (x::l) l'').

Lemma permutation_insertion_comm : forall (A:Set)(l1 l2:list A)(x:A),(insertion A x l1 l2)->forall (l4:list A),(is_permutation A l2 l4)->(exists l3:list A,(is_permutation A l1 l3) /\ (insertion A x l3 l4)).
intros A l1 l2.
generalize l1;clear l1.
induction l2;intros.
inversion H.
inversion H.
subst a.
subst x0.
subst l.
subst l2.
inversion H0.
subst x0.
subst l.
subst l''.
exists l'.
tauto.
subst x0.
subst l'.
subst a.
subst l1.
inversion H0.
subst x0.
subst l''.
subst l0.
elim (IHl2 l x H4 l' H3).
intro l3;intros.
elim H1;clear H1;intros.
elim (insertion_trans A l3 l' x H2 l4 y H6).
intro l5;intros.
elim H5;clear H5;intros.
exists l5.
split;trivial.
eapply cons_is_permutation.
apply H1.
trivial.
