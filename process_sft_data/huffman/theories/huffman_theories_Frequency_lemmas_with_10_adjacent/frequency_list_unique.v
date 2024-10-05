From Huffman Require Import AuxLib.
Require Import List.
From Huffman Require Import UniqueKey.
From Huffman Require Import Permutation.
Section Frequency.
Variable A : Type.
Variable eqA_dec : forall a b : A, {a = b} + {a <> b}.
Fixpoint id_list (a : A) (n : nat) {struct n} : list A := match n with | O => [] | S n1 => a :: id_list a n1 end.
Fixpoint add_frequency_list (a : A) (l : list (A * nat)) {struct l} : list (A * nat) := match l with | [] => (a, 1) :: [] | (b, n) :: l1 => match eqA_dec a b with | left _ => (a, S n) :: l1 | right _ => (b, n) :: add_frequency_list a l1 end end.
Fixpoint frequency_list (l : list A) : list (A * nat) := match l with | [] => [] | a :: l1 => add_frequency_list a (frequency_list l1) end.
Hint Resolve frequency_list_unique : core.
Hint Resolve in_frequency_map : core.
Fixpoint number_of_occurrences (a : A) (l : list A) {struct l} : nat := match l with | [] => 0 | b :: l1 => match eqA_dec a b with | left _ => S (number_of_occurrences a l1) | right _ => number_of_occurrences a l1 end end.
End Frequency.
Arguments id_list [A].
Arguments add_frequency_list [A].
Arguments frequency_list [A].
Arguments number_of_occurrences [A].
Hint Resolve in_frequency_map : core.
Hint Resolve frequency_list_unique : core.

Theorem add_frequency_list_perm : forall (a : A) l, permutation (a :: flat_map (fun p => id_list (fst p) (snd p)) l) (flat_map (fun p => id_list (fst p) (snd p)) (add_frequency_list a l)).
Proof using.
intros a l; generalize a; elim l; simpl in |- *; clear a l; auto.
intros (a, n) l H b.
case (eqA_dec b a); auto.
intros e; simpl in |- *; rewrite e; auto.
simpl in |- *.
intros e; apply permutation_trans with (id_list a n ++ (b :: []) ++ flat_map (fun p => id_list (fst p) (snd p)) l); [ idtac | simpl in |- *; auto ].
change (permutation ((b :: []) ++ id_list a n ++ flat_map (fun p => id_list (fst p) (snd p)) l) (id_list a n ++ (b :: []) ++ flat_map (fun p => id_list (fst p) (snd p)) l)) in |- *.
Admitted.

Theorem add_frequency_list_in_inv : forall (a1 a2 : A) (b1 : nat) l, In (a1, b1) (add_frequency_list a2 l) -> a1 = a2 \/ In (a1, b1) l.
Proof using.
intros a1 a2 b1 l; elim l; simpl in |- *; auto.
intros [H1| H1]; auto; injection H1; auto.
intros (a3, b3) l1 Rec; simpl in |- *; auto.
case (eqA_dec a2 a3); simpl in |- *; auto.
intros e H; cut (In (a1, b1) ((a2, S b3) :: l1)); auto.
simpl in |- *; intros [H1| H1]; auto.
injection H1; auto.
Admitted.

Theorem add_frequency_list_unique_key : forall (a : A) l, unique_key l -> unique_key (add_frequency_list a l).
Proof using.
intros a l; elim l; simpl in |- *; auto.
intros (a1, n1) l1 Rec H; case (eqA_dec a a1).
intros e; apply unique_key_perm with (l1 := (a, S n1) :: l1); auto.
apply unique_key_cons; auto.
intros b; red in |- *; intros H0; case (unique_key_in _ _ _ _ b _ H); auto.
rewrite <- e; auto.
apply unique_key_inv with (1 := H); auto.
intros n; apply unique_key_cons; auto.
intros b; red in |- *; intros H0; case add_frequency_list_in_inv with (1 := H0); auto.
intros H2; case (unique_key_in _ _ _ _ b _ H); auto.
Admitted.

Theorem add_frequency_list_1 : forall a l, (forall ca, ~ In (a, ca) l) -> In (a, 1) (add_frequency_list a l).
Proof using.
intros a l; generalize a; elim l; clear a l; simpl in |- *; auto.
intros (a1, l1) l0 H a H0.
case (eqA_dec a a1); auto.
intros H1; case (H0 l1); left; apply f_equal2 with (f := pair (A:=A) (B:=nat)); auto.
intros n; apply in_cons; auto; apply H; auto.
Admitted.

Theorem add_frequency_list_in : forall m a n, unique_key m -> In (a, n) m -> In (a, S n) (add_frequency_list a m).
Proof using.
intros m; elim m; clear m; simpl in |- *; auto.
intros (a1, l1) l Rec a n H H1; case (eqA_dec a a1); simpl in |- *; auto.
intros H2; case H1; auto.
intros H3; left; apply f_equal2 with (f := pair (A:=A) (B:=nat)); injection H3; auto.
rewrite H2; intros H3; case unique_key_in with (1 := H) (b2 := n); auto.
intros n0; right; apply Rec.
apply unique_key_inv with (1 := H); auto.
case H1; auto.
Admitted.

Theorem add_frequency_list_not_in : forall m a b n, a <> b -> In (a, n) m -> In (a, n) (add_frequency_list b m).
Proof using.
intros m; elim m; clear m; simpl in |- *; auto.
intros (a1, l1) l H a0 b n H0 [H1| H1]; case (eqA_dec b a1); simpl in |- *; auto.
intros H2; case H0; injection H1; auto.
Admitted.

Theorem frequency_list_in : forall a n m, In (a, n) (frequency_list m) -> In a m.
Proof using.
intros a n m; generalize n; elim m; clear m n; simpl in |- *; auto.
intros a0 l H n H0; case add_frequency_list_in_inv with (1 := H0); auto.
Admitted.

Theorem frequency_list_perm : forall l : list A, permutation l (flat_map (fun p => id_list (fst p) (snd p)) (frequency_list l)).
Proof using.
intros l; elim l; simpl in |- *; auto.
intros a l0 H.
Admitted.

Theorem in_frequency_map : forall l a, In a l -> In a (map fst (frequency_list l)).
Proof using.
intros l; elim l; simpl in |- *; auto.
intros a l0 H a0 [H0| H0]; auto.
rewrite H0; elim (frequency_list l0); simpl in |- *; auto.
intros (a1, l1) l2; simpl in |- *; auto.
case (eqA_dec a0 a1); simpl in |- *; auto.
cut (In a0 (map (fst (A:=A) (B:=nat)) (frequency_list l0))); auto.
elim (frequency_list l0); simpl in |- *; auto.
intros (a1, l1) l2; simpl in |- *; auto.
case (eqA_dec a a1); simpl in |- *; auto.
intros e H1 [H2| H2]; auto; left; rewrite <- H2; auto.
Admitted.

Theorem in_frequency_map_inv : forall l a, In a (map (fst (B:=_)) (frequency_list l)) -> In a l.
Proof using.
intros l a H; case in_map_inv with (1 := H); auto.
intros (a1, l1) (Hl1, Hl2); simpl in |- *.
Admitted.

Theorem number_of_occurrences_O : forall a l, ~ In a l -> number_of_occurrences a l = 0.
Proof using.
intros a l; elim l; simpl in |- *; auto.
intros a0 l0 H H0; case (eqA_dec a a0); auto.
Admitted.

Theorem number_of_occurrences_permutation_ex : forall (m : list A) (a : A), exists m1 : list A, permutation m (id_list a (number_of_occurrences a m) ++ m1) /\ ~ In a m1.
Proof using.
intros m; elim m; simpl in |- *; auto.
intros a; exists []; split; auto with datatypes.
intros a l H a0.
case (eqA_dec a0 a); simpl in |- *; intros H1.
case (H a0); intros m1 (H2, H3).
exists m1; split; auto.
pattern a0 at 1 in |- *; rewrite H1; auto.
case (H a0); intros m1 (H2, H3).
exists (a :: m1); split; auto.
apply permutation_trans with ((a :: m1) ++ id_list a0 (number_of_occurrences a0 l)); auto.
simpl in |- *; apply permutation_skip; auto.
apply permutation_trans with (1 := H2); auto.
Admitted.

Theorem number_of_occurrences_app : forall l1 l2 a, number_of_occurrences a (l1 ++ l2) = number_of_occurrences a l1 + number_of_occurrences a l2.
Proof using.
intros l1; elim l1; simpl in |- *; auto.
Admitted.

Theorem number_of_occurrences_permutation : forall l1 l2 a, permutation l1 l2 -> number_of_occurrences a l1 = number_of_occurrences a l2.
Proof using.
intros l1 l2 a H; generalize a; elim H; clear H a l1 l2; simpl in |- *; auto.
intros a L1 L2 H H0 a0; case (eqA_dec a a0); simpl in |- *; auto; case (eqA_dec a0 a); simpl in |- *; auto.
intros a b L a0; case (eqA_dec a0 a); simpl in |- *; auto; case (eqA_dec a0 b); simpl in |- *; auto.
Admitted.

Theorem frequency_number_of_occurrences : forall a m, In a m -> In (a, number_of_occurrences a m) (frequency_list m).
Proof using.
intros a m; generalize a; elim m; clear m a; simpl in |- *; auto.
intros a l H a0 H0; case (eqA_dec a0 a); simpl in |- *; auto.
intros e; case (In_dec eqA_dec a0 l).
intros H1; rewrite e; apply add_frequency_list_in; auto.
apply (H a); rewrite <- e; auto.
intros H1; rewrite number_of_occurrences_O; auto.
rewrite e; apply add_frequency_list_1.
intros ca; contradict H1; auto.
rewrite e; apply frequency_list_in with (1 := H1).
intros H1; case H0; auto.
intros H2; case H1; auto.
Admitted.

Theorem frequency_list_unique : forall l : list A, unique_key (frequency_list l).
Proof using.
intros l; elim l; simpl in |- *; auto.
intros a l0 H; apply add_frequency_list_unique_key; auto.
