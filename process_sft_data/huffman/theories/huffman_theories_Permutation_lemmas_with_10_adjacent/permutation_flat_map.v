From Huffman Require Export AuxLib.
Section permutation.
Variable A : Type.
Inductive permutation : list A -> list A -> Prop := | permutation_nil : permutation [] [] | permutation_skip : forall (a : A) (l1 l2 : list A), permutation l2 l1 -> permutation (a :: l2) (a :: l1) | permutation_swap : forall (a b : A) (l : list A), permutation (a :: b :: l) (b :: a :: l) | permutation_trans : forall l1 l2 l3 : list A, permutation l1 l2 -> permutation l2 l3 -> permutation l1 l3.
Hint Constructors permutation : core.
Hint Resolve permutation_refl : core.
Hint Resolve permutation_app_comp : core.
Fixpoint split_one (l : list A) : list (A * list A) := match l with | [] => [] | a :: l1 => (a, l1) :: map (fun p : A * list A => (fst p, a :: snd p)) (split_one l1) end.
Fixpoint all_permutations_aux (l : list A) (n : nat) {struct n} : list (list A) := match n with | O => [] :: [] | S n1 => flat_map (fun p : A * list A => map (cons (fst p)) (all_permutations_aux (snd p) n1)) (split_one l) end.
Definition all_permutations (l : list A) := all_permutations_aux l (length l).
Definition permutation_dec : (forall a b : A, {a = b} + {a <> b}) -> forall l1 l2 : list A, {permutation l1 l2} + {~ permutation l1 l2}.
Proof.
intros H l1 l2.
case (In_dec (list_eq_dec H) l1 (all_permutations l2)).
intros i; left; apply all_permutations_permutation; auto.
intros i; right; contradict i; apply permutation_all_permutations; auto.
Defined.
End permutation.
Hint Constructors permutation : core.
Hint Resolve permutation_refl : core.
Hint Resolve permutation_app_comp : core.
Hint Resolve permutation_app_swap : core.
Arguments permutation [A].
Arguments split_one [A].
Arguments all_permutations [A].
Arguments permutation_dec [A].
Hint Resolve permutation_map : core.

Theorem split_one_permutation : forall (a : A) (l1 l2 : list A), In (a, l1) (split_one l2) -> permutation (a :: l1) l2.
Proof using.
intros a l1 l2; generalize a l1; elim l2; clear a l1 l2; simpl in |- *; auto.
intros a l1 H1; case H1.
intros a l H a0 l1 [H0| H0].
injection H0; intros H1 H2; rewrite H2; rewrite H1; auto.
generalize H H0; elim (split_one l); simpl in |- *; auto.
intros H1 H2; case H2.
intros a1 l0 H1 H2 [H3| H3]; auto.
injection H3; intros H4 H5; (rewrite <- H4; rewrite <- H5).
apply permutation_trans with (a :: fst a1 :: snd a1); auto.
apply permutation_skip.
apply H2; auto.
Admitted.

Theorem split_one_in_ex : forall (a : A) (l1 : list A), In a l1 -> exists l2 : list A, In (a, l2) (split_one l1).
Proof using.
intros a l1; elim l1; simpl in |- *; auto.
intros H; case H.
intros a0 l H [H0| H0]; auto.
exists l; left; apply f_equal2 with (f := pair (A:=A) (B:=list A)); auto.
case H; auto.
intros x H1; exists (a0 :: x); right; auto.
Admitted.

Lemma all_permutations_aux_permutation : forall (n : nat) (l1 l2 : list A), n = length l2 -> In l1 (all_permutations_aux l2 n) -> permutation l1 l2.
Proof using.
intros n; elim n; simpl in |- *; auto.
intros l1 l2; case l2.
simpl in |- *; intros H0 [H1| H1].
rewrite <- H1; auto.
case H1.
simpl in |- *; intros; discriminate.
intros n0 H l1 l2 H0 H1.
case in_flat_map_ex with (1 := H1).
clear H1; intros x; case x; clear x; intros a1 l3 (H1, H2).
case in_map_inv with (1 := H2).
simpl in |- *; intros y (H3, H4).
rewrite H4; auto.
apply permutation_trans with (a1 :: l3); auto.
apply permutation_skip; auto.
apply H with (2 := H3).
apply eq_add_S.
apply trans_equal with (1 := H0).
change (length l2 = length (a1 :: l3)) in |- *.
apply permutation_length; auto.
apply permutation_sym; apply split_one_permutation; auto.
Admitted.

Theorem all_permutations_permutation : forall l1 l2 : list A, In l1 (all_permutations l2) -> permutation l1 l2.
Proof using.
Admitted.

Lemma permutation_all_permutations_aux : forall (n : nat) (l1 l2 : list A), n = length l2 -> permutation l1 l2 -> In l1 (all_permutations_aux l2 n).
Proof using.
intros n; elim n; simpl in |- *; auto.
intros l1 l2; case l2.
intros H H0; rewrite permutation_nil_inv with (1 := H0); auto with datatypes.
simpl in |- *; intros; discriminate.
intros n0 H l1; case l1.
intros l2 H0 H1; rewrite permutation_nil_inv with (1 := permutation_sym _ _ H1) in H0; discriminate.
clear l1; intros a1 l1 l2 H1 H2.
case (split_one_in_ex a1 l2); auto.
apply permutation_in with (1 := H2); auto with datatypes.
intros x H0.
apply in_flat_map_in with (b := (a1, x)); auto.
apply in_map; simpl in |- *.
apply H; auto.
apply eq_add_S.
apply trans_equal with (1 := H1).
change (length l2 = length (a1 :: x)) in |- *.
apply permutation_length; auto.
apply permutation_sym; apply split_one_permutation; auto.
apply permutation_inv with (a := a1).
apply permutation_trans with (1 := H2).
Admitted.

Theorem permutation_all_permutations : forall l1 l2 : list A, permutation l1 l2 -> In l1 (all_permutations l2).
Proof using.
Admitted.

Definition permutation_dec : (forall a b : A, {a = b} + {a <> b}) -> forall l1 l2 : list A, {permutation l1 l2} + {~ permutation l1 l2}.
Proof.
intros H l1 l2.
case (In_dec (list_eq_dec H) l1 (all_permutations l2)).
intros i; left; apply all_permutations_permutation; auto.
Admitted.

Theorem permutation_map : forall (A B : Type) (f : A -> B) l1 l2, permutation l1 l2 -> permutation (map f l1) (map f l2).
Proof using.
intros A B f l1 l2 H; elim H; simpl in |- *; auto.
Admitted.

Lemma permutation_map_ex_aux : forall (A B : Type) (f : A -> B) l1 l2 l3, permutation l1 l2 -> l1 = map f l3 -> exists l4, permutation l4 l3 /\ l2 = map f l4.
Proof using.
intros A1 B1 f l1 l2 l3 H; generalize l3; elim H; clear H l1 l2 l3.
intros l3; case l3; simpl in |- *; auto.
intros H; exists []; auto.
intros; discriminate.
intros a0 l1 l2 H H0 l3; case l3; simpl in |- *; auto.
intros; discriminate.
intros a1 l H1; case (H0 l); auto.
injection H1; auto.
intros l5 (H2, H3); exists (a1 :: l5); split; simpl in |- *; auto.
apply f_equal2 with (f := cons (A:=B1)); auto; injection H1; auto.
intros a0 b l l3; case l3.
intros; discriminate.
intros a1 l0; case l0; simpl in |- *.
intros; discriminate.
intros a2 l1 H; exists (a2 :: a1 :: l1); split; simpl in |- *; auto.
repeat apply f_equal2 with (f := cons (A:=B1)); injection H; auto.
intros l1 l2 l3 H H0 H1 H2 l0 H3.
case H0 with (1 := H3); auto.
intros l4 (HH1, HH2).
case H2 with (1 := HH2); auto.
intros l5 (HH3, HH4); exists l5; split; auto.
Admitted.

Theorem permutation_map_ex : forall (A B : Type) (f : A -> B) l1 l2, permutation (map f l1) l2 -> exists l3, permutation l3 l1 /\ l2 = map f l3.
Proof using.
Admitted.

Theorem fold_left_permutation : forall (A B : Type) (f : A -> B -> A), (forall (a : A) (b1 b2 : B), f (f a b1) b2 = f (f a b2) b1) -> forall (a : A) (l1 l2 : list B), permutation l1 l2 -> fold_left f l1 a = fold_left f l2 a.
Proof using.
intros A B f Hf a l1 l2 H; generalize a; elim H; clear H a l1 l2; simpl in |- *; auto.
intros a b l a0; rewrite Hf; auto.
Admitted.

Theorem permutation_flat_map : forall (A B : Type) (f : A -> list B) l1 l2, permutation l1 l2 -> permutation (flat_map f l1) (flat_map f l2).
Proof using.
intros A B f l1 l2 H; elim H; simpl in |- *; auto.
intros a b l; auto.
repeat rewrite <- app_ass.
apply permutation_app_comp; auto.
intros k3 l4 l5 H0 H1 H2 H3; apply permutation_trans with (1 := H1); auto.
