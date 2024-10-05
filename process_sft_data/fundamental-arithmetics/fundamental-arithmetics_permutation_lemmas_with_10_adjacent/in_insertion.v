Require Import Wf_nat.
Require Import missing.
Require Export List Permutation.
Inductive insertion (A:Set) : A -> list A -> list A -> Prop := head_insertion : forall (x:A)(l:list A),(insertion A x l (x::l)) |tail_insertion : forall (x y:A)(l l':list A),(insertion A x l l')->(insertion A x (y::l) (y::l')).
Inductive is_set (A:Set) : list A->Prop := nil_is_set : (is_set A nil) |cons_is_set : forall (x:A)(l:list A),(is_set A l)->~(In x l)->(is_set A (x::l)).
Inductive is_permutation (A:Set) : list A->list A->Prop := nil_is_permutation : (is_permutation A nil nil) |cons_is_permutation : forall (l l':list A),(is_permutation A l l')->forall (x:A)(l'':(list A)),(insertion A x l' l'')->(is_permutation A (x::l) l'').

Lemma insertion_snoc : forall (A:Set)(x:A)(xs:list A),(insertion _ x xs (app xs (cons x nil))).
induction xs.
simpl.
apply head_insertion.
simpl.
apply tail_insertion.
Admitted.

Lemma insertion_in : forall (A:Set)(x:A)(l l':list A),(insertion A x l l')->(In x l').
intros.
Admitted.

Lemma insertion_inclusion : forall (A:Set)(x:A)(l l':list A),(insertion A x l l')->forall (y:A),(In y l)->(In y l').
induction l;simpl;try tauto;intros.
inversion H;simpl;try tauto.
case H0;try tauto.
Admitted.

Lemma in_insertion_inv : forall (A:Set)(x y:A)(l l':list A),(insertion A y l l')->(In x l')->(x=y)\/(In x l).
intros.
induction H;simpl in H0.
case H0;intro H1;try (symmetry in H1);tauto.
Admitted.

Lemma is_set_insertion : forall (A:Set)(l l':list A)(x:A),(insertion A x l l')->(is_set A l')->(is_set A l).
induction 1;intros.
inversion H;trivial.
inversion H0.
apply cons_is_set.
apply IHinsertion;trivial.
Admitted.

Lemma is_set_insertion_in : forall (A:Set)(l l':list A)(x:A),(insertion A x l l')->(is_set A l')->~(In x l).
induction l;simpl;try tauto;intros.
inversion H;rewrite <- H3 in H0;inversion H0.
simpl in H7;trivial.
intro.
case H10;intro.
apply H9;rewrite H11;eapply insertion_in;apply H5.
Admitted.

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
Admitted.

Lemma is_set_eq_impl_permutation : forall (A:Set)(l l':list A),(forall (x:A),(In x l)<->(In x l'))->(is_set A l)->(is_set A l')->(is_permutation A l l').
induction l;intros;simpl in H.
destruct l'.
apply nil_is_permutation.
elim (H a);intros.
elim H3;simpl;tauto.
inversion H0.
symmetry in H2;rewrite H2 in H;elim (H a);intros.
rewrite H2 in H6;rewrite H2.
assert (In x l');auto.
elim (in_insertion A x l' H8).
intro l'';intro.
apply cons_is_permutation with l'';trivial.
apply IHl;trivial.
split;intro.
elim (H x0);intros.
elim (in_insertion_inv A x0 x l'' l');auto.
intro;rewrite H13 in H10;rewrite H2 in H5;tauto.
elim (H x0);intros.
case H12;try tauto.
apply (insertion_inclusion A x l'' l');trivial.
intro;rewrite <- H13 in H10.
elim (is_set_insertion_in A l'' l' x);trivial.
Admitted.

Lemma is_permutation_refl : forall (A:Set)(l:list A),(is_permutation A l l).
induction l.
apply nil_is_permutation.
Admitted.

Lemma insertion_is_permutation : forall (A:Set)(l l':list A)(x:A),(insertion A x l l')->(is_permutation A (x::l) l').
induction 1.
apply cons_is_permutation with l;[apply is_permutation_refl | apply head_insertion].
Admitted.

Lemma insertion_trans : forall (A:Set)(l0 l1:list A)(x:A),(insertion A x l0 l1)->forall (l2:list A)(y:A),(insertion A y l1 l2)->exists l3:list A,(insertion A y l0 l3)/\(insertion A x l3 l2).
induction 1;intros.
inversion H.
exists (y::l);split;[apply head_insertion | apply tail_insertion;apply head_insertion].
exists l';split;[trivial | apply head_insertion].
inversion H0.
exists (y0::y::l);split;[apply head_insertion | apply tail_insertion;apply tail_insertion;trivial].
elim (IHinsertion l'0 y0 H5);intro l3;intro.
elim H6;intros.
Admitted.

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
Admitted.

Lemma is_permutation_sym : forall (A:Set)(l l':list A),(is_permutation A l l')->(is_permutation A l' l).
Admitted.

Lemma in_insertion : forall (A:Set)(x:A)(l:list A),(In x l)->exists l':list A,(insertion A x l' l).
induction l;simpl;try tauto;intros.
case H;intro.
rewrite H0;exists l;apply head_insertion.
elim (IHl H0);intro l';intro.
exists (a::l');apply tail_insertion;trivial.
