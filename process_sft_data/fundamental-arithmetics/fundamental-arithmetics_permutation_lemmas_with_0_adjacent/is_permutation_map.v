Require Import Wf_nat.
Require Import missing.
Require Export List Permutation.
Inductive insertion (A:Set) : A -> list A -> list A -> Prop := head_insertion : forall (x:A)(l:list A),(insertion A x l (x::l)) |tail_insertion : forall (x y:A)(l l':list A),(insertion A x l l')->(insertion A x (y::l) (y::l')).
Inductive is_set (A:Set) : list A->Prop := nil_is_set : (is_set A nil) |cons_is_set : forall (x:A)(l:list A),(is_set A l)->~(In x l)->(is_set A (x::l)).
Inductive is_permutation (A:Set) : list A->list A->Prop := nil_is_permutation : (is_permutation A nil nil) |cons_is_permutation : forall (l l':list A),(is_permutation A l l')->forall (x:A)(l'':(list A)),(insertion A x l' l'')->(is_permutation A (x::l) l'').

Lemma is_permutation_map : forall (B:Set)(ys1 ys2:list B),(is_permutation B ys1 ys2)->forall (A:Set)(f:A->B)(xs1:list A),(ys1 = map f xs1)->exists xs2:list A,(is_permutation A xs1 xs2)/\ys2 = map f xs2.
induction 1.
intros.
destruct xs1;try (discriminate H).
exists (nil (A:=A)).
split.
apply nil_is_permutation.
reflexivity.
intros.
destruct xs1;try (discriminate H1).
simpl in H1.
injection H1;clear H1;intros.
subst x.
elim (IHis_permutation _ _ _ H1).
intro xs2.
intros.
elim H2;clear H2;intros.
subst l'.
elim (insertion_map _ _ _ _ H0 _ f a (refl_equal (f a)) xs2 (refl_equal (map f xs2))).
intros.
elim H3;clear H3;intros.
exists x.
split;auto.
eapply cons_is_permutation;eauto.
