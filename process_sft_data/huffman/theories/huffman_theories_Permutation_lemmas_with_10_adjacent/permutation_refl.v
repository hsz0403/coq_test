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

Theorem permutation_sym : forall l m : list A, permutation l m -> permutation m l.
Proof using.
intros l1 l2 H'; elim H'.
apply permutation_nil.
intros a l1' l2' H1 H2.
apply permutation_skip with (1 := H2).
intros a b l1'.
apply permutation_swap.
intros l1' l2' l3' H1 H2 H3 H4.
Admitted.

Theorem permutation_length : forall l m : list A, permutation l m -> length l = length m.
Proof using.
intros l m H'; elim H'; simpl in |- *; auto.
intros l1 l2 l3 H'0 H'1 H'2 H'3.
Admitted.

Theorem permutation_nil_inv : forall l : list A, permutation l [] -> l = [].
Proof using.
intros l H; generalize (permutation_length _ _ H); case l; simpl in |- *; auto.
Admitted.

Lemma permutation_one_inv_aux : forall l1 l2 : list A, permutation l1 l2 -> forall a : A, l1 = a :: [] -> l2 = a :: [].
Proof using.
intros l1 l2 H; elim H; clear H l1 l2; auto.
intros a l3 l4 H0 H1 b H2.
apply f_equal2 with (f := cons (A:=A)).
injection H2; auto.
apply permutation_nil_inv; auto.
injection H2; intros H3 H4; rewrite <- H3; auto.
apply permutation_sym; auto.
Admitted.

Theorem permutation_one_inv : forall (a : A) (l : list A), permutation (a :: []) l -> l = a :: [].
Proof using.
Admitted.

Theorem permutation_in : forall (a : A) (l m : list A), permutation l m -> In a l -> In a m.
Proof using.
Admitted.

Theorem permutation_app_comp : forall l1 l2 l3 l4, permutation l1 l2 -> permutation l3 l4 -> permutation (l1 ++ l3) (l2 ++ l4).
Proof using.
intros l1 l2 l3 l4 H1; generalize l3 l4; elim H1; clear H1 l1 l2 l3 l4; simpl in |- *; auto.
intros a b l l3 l4 H.
cut (permutation (l ++ l3) (l ++ l4)); auto.
intros; apply permutation_trans with (a :: b :: l ++ l4); auto.
elim l; simpl in |- *; auto.
intros l1 l2 l3 H H0 H1 H2 l4 l5 H3.
Admitted.

Theorem permutation_app_swap : forall l1 l2, permutation (l1 ++ l2) (l2 ++ l1).
Proof using.
intros l1; elim l1; auto.
intros; rewrite <- app_nil_end; auto.
intros a l H l2.
replace (l2 ++ a :: l) with ((l2 ++ a :: []) ++ l).
apply permutation_trans with (l ++ l2 ++ a :: []); auto.
apply permutation_trans with (((a :: []) ++ l2) ++ l); auto.
simpl in |- *; auto.
apply permutation_trans with (l ++ (a :: []) ++ l2); auto.
apply permutation_sym; auto.
replace (l2 ++ a :: l) with ((l2 ++ a :: []) ++ l).
apply permutation_app_comp; auto.
elim l2; simpl in |- *; auto.
intros a0 l0 H0.
apply permutation_trans with (a0 :: a :: l0); auto.
apply (app_ass l2 (a :: []) l).
Admitted.

Theorem permutation_transposition : forall a b l1 l2 l3, permutation (l1 ++ a :: l2 ++ b :: l3) (l1 ++ b :: l2 ++ a :: l3).
Proof using.
intros a b l1 l2 l3.
apply permutation_app_comp; auto.
change (permutation ((a :: []) ++ l2 ++ (b :: []) ++ l3) ((b :: []) ++ l2 ++ (a :: []) ++ l3)) in |- *.
repeat rewrite <- app_ass.
apply permutation_app_comp; auto.
apply permutation_trans with ((b :: []) ++ (a :: []) ++ l2); auto.
apply permutation_app_swap; auto.
repeat rewrite app_ass.
apply permutation_app_comp; auto.
Admitted.

Theorem in_permutation_ex : forall a l, In a l -> exists l1 : list A, permutation (a :: l1) l.
Proof using.
intros a l; elim l; simpl in |- *; auto.
intros H; case H; auto.
intros a0 l0 H [H0| H0].
exists l0; rewrite H0; auto.
case H; auto; intros l1 Hl1; exists (a0 :: l1).
Admitted.

Theorem permutation_refl : forall l : list A, permutation l l.
Proof using.
simple induction l.
apply permutation_nil.
intros a l1 H.
apply permutation_skip with (1 := H).
