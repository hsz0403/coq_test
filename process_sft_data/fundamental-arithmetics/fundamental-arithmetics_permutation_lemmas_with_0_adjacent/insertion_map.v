Require Import Wf_nat.
Require Import missing.
Require Export List Permutation.
Inductive insertion (A:Set) : A -> list A -> list A -> Prop := head_insertion : forall (x:A)(l:list A),(insertion A x l (x::l)) |tail_insertion : forall (x y:A)(l l':list A),(insertion A x l l')->(insertion A x (y::l) (y::l')).
Inductive is_set (A:Set) : list A->Prop := nil_is_set : (is_set A nil) |cons_is_set : forall (x:A)(l:list A),(is_set A l)->~(In x l)->(is_set A (x::l)).
Inductive is_permutation (A:Set) : list A->list A->Prop := nil_is_permutation : (is_permutation A nil nil) |cons_is_permutation : forall (l l':list A),(is_permutation A l l')->forall (x:A)(l'':(list A)),(insertion A x l' l'')->(is_permutation A (x::l) l'').

Lemma insertion_map : forall (B:Set)(y:B)(ys yss:list B),(insertion _ y ys yss)->forall (A:Set)(f:A->B)(x:A),y=f x->forall (xs:list A),ys = map f xs->exists xss:list A,yss = map f xss /\ insertion _ x xs xss.
induction 1;intros.
exists (cons x0 xs).
simpl.
split.
subst x;subst l;auto.
apply head_insertion.
destruct xs.
discriminate H1.
simpl in H1.
injection H1;clear H1;intros.
elim (IHinsertion _ _ _ H0 _ H1).
intro xss;intros.
elim H3;clear H3;intros.
exists (cons a xss).
simpl.
split.
subst y;subst l';auto.
apply tail_insertion.
auto.
