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
apply permutation_sym; apply split_one_permutation; auto.
