Require Import Wf_nat.
Require Import missing.
Require Export List Permutation.
Inductive insertion (A:Set) : A -> list A -> list A -> Prop := head_insertion : forall (x:A)(l:list A),(insertion A x l (x::l)) |tail_insertion : forall (x y:A)(l l':list A),(insertion A x l l')->(insertion A x (y::l) (y::l')).
Inductive is_set (A:Set) : list A->Prop := nil_is_set : (is_set A nil) |cons_is_set : forall (x:A)(l:list A),(is_set A l)->~(In x l)->(is_set A (x::l)).
Inductive is_permutation (A:Set) : list A->list A->Prop := nil_is_permutation : (is_permutation A nil nil) |cons_is_permutation : forall (l l':list A),(is_permutation A l l')->forall (x:A)(l'':(list A)),(insertion A x l' l'')->(is_permutation A (x::l) l'').

Lemma is_permutation_reverse_impl_is_permutation : forall (A:Set)(l l':list A),(is_permutation A (rev l) (rev l'))->(is_permutation A l l').
intros.
eapply is_permutation_trans.
apply is_permutation_reverse.
apply is_permutation_sym.
eapply is_permutation_trans.
apply is_permutation_reverse.
apply is_permutation_sym.
Admitted.

Lemma is_permutation_impl_is_permutation_reverse : forall (A:Set)(l l':list A),(is_permutation A l l')->(is_permutation A (rev l) (rev l')).
intros.
apply is_permutation_reverse_impl_is_permutation.
rewrite rev_involutive.
rewrite rev_involutive.
Admitted.

Lemma is_permutation_cons_snoc : forall (A:Set)(x:A)(xs:list A),(is_permutation A (cons x xs) (app xs (cons x nil))).
intros.
eapply cons_is_permutation.
apply is_permutation_refl.
Admitted.

Lemma insertion_append : forall (A:Set)(x:A)(xs xss:list A),(insertion A x xs xss)->forall (yss:list A),(insertion A x (app xs yss) (app xss yss)).
induction 1.
simpl.
intros.
apply head_insertion.
intros.
simpl.
apply tail_insertion.
Admitted.

Lemma is_permutation_append : forall (A:Set)(xs ys:list A),(is_permutation A xs ys)->forall (xs' ys':list A),(is_permutation A xs' ys')->(is_permutation A (app xs xs') (app ys ys')).
induction 1;intros.
simpl.
auto.
simpl.
eapply cons_is_permutation.
apply IHis_permutation.
apply H1.
apply insertion_append.
Admitted.

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
Admitted.

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
Admitted.

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
Admitted.

Lemma Permutation_impl_permutation : forall (A:Set)(l l':list A),(Permutation l l')->(is_permutation _ l l').
induction 1.
apply nil_is_permutation.
eapply cons_is_permutation.
apply IHPermutation.
apply head_insertion.
eapply cons_is_permutation.
apply is_permutation_refl.
apply tail_insertion.
apply head_insertion.
Admitted.

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
Admitted.

Lemma permutation_impl_Permutation : forall (A:Set)(l l':list A),(is_permutation _ l l')->(Permutation l l').
induction 1.
apply perm_nil.
elim (insertion_append_decompose _ _ _ _ H0).
intro l1;intros.
elim H1.
intro l2;intros.
elim H2;clear H2;intros.
subst l';subst l''.
apply Permutation_cons_app.
auto.
