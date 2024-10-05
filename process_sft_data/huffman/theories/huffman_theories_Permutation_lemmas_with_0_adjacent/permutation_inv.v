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

Theorem permutation_inv : forall (a : A) (l1 l2 : list A), permutation (a :: l1) (a :: l2) -> permutation l1 l2.
Proof using.
intros a l1 l2 H; case permutation_cons_ex with (1 := H).
intros l3 (l4, (Hl1, Hl2)).
apply permutation_trans with (1 := Hl2).
generalize Hl1; case l3; simpl in |- *; auto.
intros H1; injection H1; intros H2; rewrite H2; auto.
intros a0 l5 H1; injection H1; intros H2 H3; rewrite H2; rewrite H3; auto.
apply permutation_trans with (a0 :: l4 ++ l5); auto.
apply permutation_skip; apply permutation_app_swap.
apply (permutation_app_swap (a0 :: l4) l5).
