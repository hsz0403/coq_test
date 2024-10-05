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

Lemma permutation_in : forall (A:Set)(l l':list A),(is_permutation A l l')->forall (x:A),(In x l)<->(In x l').
induction l;simpl;intros.
inversion H;simpl;tauto.
inversion H;simpl.
split;intro.
case H5;intro.
eapply insertion_in;rewrite H6 in H4;apply H4.
elim (IHl l'0 H2 x);intros.
eapply insertion_inclusion;eauto.
case (in_insertion_inv A x a l'0 l' H4 H5);intro.
rewrite H6;tauto.
elim (IHl l'0 H2 x);intros.
Admitted.

Lemma permutation_insertion_aux : forall (A:Set)(l l' l'':list A)(x:A),(insertion A x l l')->(insertion A x l l'')->(is_permutation A l' l'').
intros.
eapply permutation_insertion;eauto.
Admitted.

Lemma length_recursion : forall (A:Set),forall (P:list A->Prop),(forall (x:list A),(forall (y:list A),(length y)<(length x)->(P y))->(P x))->(forall (a:list A),(P a)).
intros.
Admitted.

Lemma insertion_length : forall (A:Set)(l l':list A)(x:A),(insertion A x l l')->(length l')=(S (length l)).
induction 1;simpl;trivial.
Admitted.

Lemma permutation_length : forall (A:Set)(l l':list A),(is_permutation A l l')->(length l)=(length l').
induction 1;simpl;trivial.
Admitted.

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
Admitted.

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
Admitted.

Lemma permutation_insertion_permutation : forall (A:Set)(l l':list A),(is_permutation A l l')->forall (x:A)(l'':list A),(insertion A x l' l'')->forall (l''':list A),(is_permutation A l'' l''')->(is_permutation A (x::l) l''').
induction 1;intros.
inversion H.
rewrite <- H3 in H0.
trivial.
elim (permutation_insertion_comm A l'' l''0 x0 H1 l''' H2).
intro l1;intro.
elim H3;clear H3;intros.
eapply cons_is_permutation.
eapply IHis_permutation.
apply H0.
apply H3.
Admitted.

Lemma is_permutation_trans : forall (A:Set)(l l':list A),(is_permutation A l l')->forall (l'':list A),(is_permutation A l' l'')->(is_permutation A l l'').
induction l.
intros.
inversion H.
rewrite <- H2 in H0;trivial.
intros.
inversion H.
induction H5;inversion H0.
eapply cons_is_permutation;try (apply IHl with l1;eauto);trivial.
eapply permutation_insertion_permutation.
apply H3.
apply tail_insertion.
apply H5.
eapply cons_is_permutation.
apply H8.
Admitted.

Lemma is_permutation_reverse : forall (A:Set)(l:list A),(is_permutation A l (rev l)).
induction l.
simpl.
apply nil_is_permutation.
simpl.
eapply cons_is_permutation.
apply IHl.
Admitted.

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
auto.
