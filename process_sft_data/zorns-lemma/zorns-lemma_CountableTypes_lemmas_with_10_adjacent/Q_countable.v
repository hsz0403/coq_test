Require Export FiniteTypes Relation_Definitions ZArith QArith IndexedFamilies.
Require Import InfiniteTypes CSB DecidableDec FunctionalExtensionality ProofIrrelevance DependentTypeChoice ClassicalChoice Arith ArithRing.
Local Close Scope Q_scope.
Set Asymmetric Patterns.
Inductive CountableT (X : Type) : Prop := | intro_nat_injection (f : X -> nat) : injective f -> CountableT X.
Definition Countable {X : Type} (S : Ensemble X) : Prop := CountableT {x:X | In S x}.

Lemma countable_exp (X Y : Type) : FiniteT X -> CountableT Y -> CountableT (X -> Y).
Proof.
intros.
induction H.
-
exists (fun _ => 0).
red; intros.
extensionality f.
destruct f.
-
destruct (countable_product (T -> Y) Y); trivial.
exists (fun g => f (fun x => g (Some x), g None)).
intros g1 g2 ?.
apply H1 in H2.
extensionality o.
destruct o; injection H2; trivial.
intros.
pose proof (equal_f H4).
apply H5.
-
destruct H1, IHFiniteT.
exists (fun h => f0 (fun x => h (f x))).
intros h1 h2 ?.
apply H3 in H4.
pose proof (equal_f H4).
simpl in H5.
extensionality y.
rewrite <- (H2 y).
Admitted.

Lemma inj_countable {X Y : Type} (f : X -> Y) : CountableT Y -> injective f -> CountableT X.
Proof.
intros [g] ?.
exists (fun x:X => g (f x)).
intros x1 x2 ?.
Admitted.

Lemma surj_countable {X Y : Type} (f : X -> Y) : CountableT X -> surjective f -> CountableT Y.
Proof.
intros.
destruct (choice (fun (y:Y) (x:X) => f x = y)) as [finv]; trivial.
apply inj_countable with finv; trivial.
intros x1 x2 ?.
Admitted.

Lemma countable_downward_closed {X : Type} (S T : Ensemble X) : Countable T -> Included S T -> Countable S.
Proof.
intros [f H] H0.
exists (fun x => match x with | exist x0 i => f (exist _ x0 (H0 _ i)) end).
intros [x1] [x2] H1.
apply H in H1.
injection H1 as H1.
Admitted.

Lemma countable_img {X Y : Type} (f : X -> Y) (S : Ensemble X) : Countable S -> Countable (Im S f).
Proof.
intros.
assert (forall x, In S x -> In (Im S f) (f x)) by auto with sets.
pose (fS := fun x => match x with | exist x0 i => exist _ (f x0) (H0 x0 i) end).
apply surj_countable with fS; trivial.
intros [? [x i y e]].
exists (exist _ x i).
simpl.
generalize (H0 x i); intro.
generalize (Im_intro X Y S f x i y e); intro.
Admitted.

Lemma countable_type_ensemble {X : Type} (S : Ensemble X) : CountableT X -> Countable S.
Proof.
intros.
apply (inj_countable (@proj1_sig _ (In S)) H).
intros [? ?] [? ?].
Admitted.

Lemma FiniteT_impl_CountableT (X : Type) : FiniteT X -> CountableT X.
Proof.
intros.
induction H.
-
exists (False_rect nat).
now intro.
-
destruct IHFiniteT.
exists (fun x => match x with | Some x0 => S (f x0) | None => 0 end).
intros [x1|] [x2|] H1; injection H1 as H1 + discriminate H1 + trivial.
now destruct (H0 _ _ H1).
-
destruct IHFiniteT as [g], H0 as [finv].
exists (fun y:Y => g (finv y)).
intros y1 y2 ?.
apply H1 in H3.
Admitted.

Lemma Finite_impl_Countable: forall {X : Type} (S : Ensemble X), Finite _ S -> Countable S.
Proof.
intros.
Admitted.

Lemma positive_countable: CountableT positive.
Proof.
exists nat_of_P.
intros n1 n2 ?.
Admitted.

Lemma Z_countable: CountableT Z.
Proof.
destruct countable_nat_product as [f], positive_countable as [g].
exists (fun n:Z => match n with | Z0 => f (0, 0) | Zpos p => f (1, g p) | Zneg p => f (2, g p) end).
Admitted.

Lemma countable_union: forall {X A:Type} (F:IndexedFamily A X), CountableT A -> (forall a:A, Countable (F a)) -> Countable (IndexedUnion F).
Proof.
intros.
destruct (choice_on_dependent_type (fun (a:A) (f:{x:X | In (F a) x} -> nat) => injective f)) as [choice_fun_inj].
-
intro.
destruct (H0 a).
now exists f.
-
destruct (choice (fun (x:{x:X | In (IndexedUnion F) x}) (a:A) => In (F a) (proj1_sig x))) as [choice_fun_a].
+
destruct x as [x [a]].
now exists a.
+
destruct countable_nat_product as [g], H as [h].
exists (fun x:{x:X | In (IndexedUnion F) x} => g (h (choice_fun_a x), choice_fun_inj _ (exist _ _ (H2 x)))).
intros x1 x2 H4.
apply H3 in H4.
injection H4 as H5 H6.
apply H in H5.
revert H6.
generalize (H2 x1), (H2 x2).
rewrite H5.
intros.
apply H1 in H6.
injection H6.
destruct x1, x2.
Admitted.

Lemma Q_countable: CountableT Q.
Proof.
destruct countable_nat_product as [f], positive_countable as [g], Z_countable as [h].
exists (fun q:Q => match q with n # d => f (h n, g d) end)%Q.
intros [n1 d1] [n2 d2] ?.
apply H in H2.
injection H2 as H2.
f_equal; auto.
