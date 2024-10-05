Require Import Wf_nat.
Require Import missing.
Require Export List Permutation.
Inductive insertion (A:Set) : A -> list A -> list A -> Prop := head_insertion : forall (x:A)(l:list A),(insertion A x l (x::l)) |tail_insertion : forall (x y:A)(l l':list A),(insertion A x l l')->(insertion A x (y::l) (y::l')).
Inductive is_set (A:Set) : list A->Prop := nil_is_set : (is_set A nil) |cons_is_set : forall (x:A)(l:list A),(is_set A l)->~(In x l)->(is_set A (x::l)).
Inductive is_permutation (A:Set) : list A->list A->Prop := nil_is_permutation : (is_permutation A nil nil) |cons_is_permutation : forall (l l':list A),(is_permutation A l l')->forall (x:A)(l'':(list A)),(insertion A x l' l'')->(is_permutation A (x::l) l'').

Lemma insertion_permutation_eq : forall (A:Set)(l l':list A)(x:A),(insertion A x l' l)->forall (l'':list A),(insertion A x l'' l)->(is_permutation A l' l'').
induction l;intros;inversion H.
inversion H0.
apply is_permutation_refl.
rewrite <- H4;destruct l.
inversion H8.
generalize (head_insertion A a0 l);intro.
assert (In x (a0::l)).
eapply insertion_in;apply H8.
case (in_insertion_inv A x a0 l (a0::l) H10 H11);intro.
rewrite H12;rewrite <- H12 in H10;rewrite <- H12 in H8;rewrite <- H12 in IHl.
assert (is_permutation A l l1).
eapply IHl;eauto.
eapply cons_is_permutation;eauto;apply head_insertion.
elim (in_insertion A x l H12);intro l2;intro.
generalize (tail_insertion A x a0 l2 l H13);intro.
assert (is_permutation A (a0::l2) l1).
eapply IHl;eauto.
apply is_permutation_sym;auto.
eapply cons_is_permutation;eauto.
rewrite H1 in H3.
inversion H0.
rewrite <- H9;apply insertion_is_permutation;trivial.
assert (is_permutation A l0 l1).
eapply IHl;eauto.
eapply cons_is_permutation;eauto;apply head_insertion.
