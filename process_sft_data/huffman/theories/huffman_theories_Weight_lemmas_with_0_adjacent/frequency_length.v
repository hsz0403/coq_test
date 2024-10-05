From Huffman Require Export Code.
From Huffman Require Export Frequency.
From Huffman Require Export ISort.
From Huffman Require Export Permutation.
From Huffman Require Export UniqueKey.
Section Weight.
Variable A : Type.
Variable eqA_dec : forall a b : A, {a = b} + {a <> b}.
Definition weight m c := length (encode eqA_dec c m).
Definition restrict_code (m : list A) (c : code A) : code A := map (fun x => (fst x, find_code eqA_dec (fst x) c)) (frequency_list eqA_dec m).
End Weight.
Arguments weight [A].
Arguments restrict_code [A].

Theorem frequency_length : forall (m : list A) (c : code A), unique_key c -> length (encode eqA_dec c m) = fold_left (fun a b => a + number_of_occurrences eqA_dec (fst b) m * length (snd b)) c 0.
Proof using.
intros m c; generalize m; elim c; clear c m; simpl in |- *; auto.
intros m; elim m; simpl in |- *; auto.
intros (a, l1) l Rec m H; simpl in |- *.
case (number_of_occurrences_permutation_ex A eqA_dec m a); intros m1 (Hm1, Hm2).
rewrite permutation_length with (1 := encode_permutation_val _ eqA_dec _ _ ((a, l1) :: l) Hm1).
rewrite encode_app; auto.
rewrite app_length; auto.
rewrite length_encode_nId.
rewrite encode_cons_inv; auto.
rewrite Rec; simpl in |- *; auto.
rewrite <- fold_plus_split with (f := fun b : A * list bool => number_of_occurrences eqA_dec (fst b) m * length (snd b)) (c := number_of_occurrences eqA_dec a m * length l1).
apply f_equal2 with (f := plus); auto.
cut (forall l2, ~ In (a, l2) l).
elim l; simpl in |- *; auto.
intros (a2, l2) l3; simpl in |- *; intros Rec1 H4.
rewrite <- fold_plus_split with (c := number_of_occurrences eqA_dec a2 m1 * length l2) (f := fun b : A * list bool => number_of_occurrences eqA_dec (fst b) m1 * length (snd b)).
rewrite <- fold_plus_split with (c := number_of_occurrences eqA_dec a2 m * length l2) (f := fun b : A * list bool => number_of_occurrences eqA_dec (fst b) m * length (snd b)).
apply f_equal2 with (f := plus); auto.
2: apply Rec1; auto.
2: intros l0; red in |- *; intros H0; case (H4 l0); auto.
2: intros l2; red in |- *; intros H0; case unique_key_in with (1 := H) (a := a) (b2 := l2); auto.
2: apply unique_key_inv with (1 := H); auto.
apply f_equal2 with (f := mult); auto.
apply trans_equal with (2 := number_of_occurrences_permutation _ eqA_dec _ _ a2 (permutation_sym _ _ _ Hm1)).
rewrite number_of_occurrences_app.
replace (number_of_occurrences eqA_dec a2 (id_list a (number_of_occurrences eqA_dec a m))) with 0; auto.
cut (a2 <> a).
elim (number_of_occurrences eqA_dec a m); simpl in |- *; auto.
intros n H0 H1; case (eqA_dec a2 a); simpl in |- *; auto.
intros e; case H1; auto.
red in |- *; intros H0; case (H4 l2); left; apply f_equal2 with (f := pair (A:=A) (B:=list bool)); auto.
