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
apply permutation_trans with (1 := HH3); auto.
