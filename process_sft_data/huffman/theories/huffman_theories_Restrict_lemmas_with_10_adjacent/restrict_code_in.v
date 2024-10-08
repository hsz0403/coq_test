From Huffman Require Export Code.
From Huffman Require Export Frequency.
From Huffman Require Export ISort.
From Huffman Require Export Permutation.
From Huffman Require Export UniqueKey.
From Huffman Require Export PBTree2BTree.
Section Restrict.
Variable A : Type.
Variable empty : A.
Variable eqA_dec : forall a b : A, {a = b} + {a <> b}.
Variable m : list A.
Definition restrict_code (m : list A) (c : code A) : code A := map (fun x => (fst x, find_code eqA_dec (fst x) c)) (frequency_list eqA_dec m).
End Restrict.
Arguments restrict_code [A].

Theorem restrict_code_unique_key : forall c : code A, unique_key (restrict_code m c).
Proof using.
intros c; apply ulist_unique_key.
unfold restrict_code in |- *.
replace (map (fst (B:=_)) (map (fun x : A * nat => (fst x, find_code eqA_dec (fst x) c)) (frequency_list eqA_dec m))) with (map (fst (B:=_)) (frequency_list eqA_dec m)).
apply unique_key_ulist; auto.
elim (frequency_list eqA_dec m); simpl in |- *; auto with datatypes.
Admitted.

Theorem restrict_code_encode_incl : forall (m1 : list A) (c : code A), incl m1 m -> encode eqA_dec c m1 = encode eqA_dec (restrict_code m c) m1.
Proof using.
intros m1 c; elim m1; simpl in |- *; auto.
intros a l H H0.
apply f_equal2 with (f := app (A:=bool)); auto with datatypes.
apply restrict_code_in; auto with datatypes.
Admitted.

Theorem restrict_code_encode : forall c : code A, encode eqA_dec c m = encode eqA_dec (restrict_code m c) m.
Proof using.
Admitted.

Theorem restrict_unique_prefix : forall c : code A, not_null c -> in_alphabet m c -> unique_prefix c -> unique_prefix (restrict_code m c).
Proof using.
intros c HH HH0 (HH1, HH2); split.
intros a1 a2 lb1 lb2 H0 H1 H2; apply HH1 with (lb1 := lb1) (lb2 := lb2); auto.
unfold restrict_code in H0.
case in_map_inv with (1 := H0).
intros x; case x; simpl in |- *.
intros a0 n (HP1, HP2).
rewrite HP2.
case (HH0 a0); auto.
apply frequency_list_in with (1 := HP1).
intros x0 H; rewrite find_code_correct2 with (2 := H); auto.
unfold restrict_code in H1.
case in_map_inv with (1 := H1).
intros x; case x; simpl in |- *.
intros a0 n (HP1, HP2).
rewrite HP2.
case (HH0 a0); auto.
apply frequency_list_in with (1 := HP1).
intros x0 H; rewrite find_code_correct2 with (2 := H); auto.
unfold restrict_code in |- *.
Admitted.

Theorem frequency_list_restric_code_map : forall c, map (fst (B:=_)) (frequency_list eqA_dec m) = map (fst (B:=_)) (restrict_code m c).
Proof using.
intros c; unfold restrict_code in |- *; elim (frequency_list eqA_dec m); simpl in |- *; auto.
Admitted.

Theorem restrict_not_null : forall c, m <> [] -> restrict_code m c <> [].
Proof using.
case m; simpl in |- *; auto.
unfold restrict_code in |- *.
intros a0 l c H H1.
absurd (In ((fun x : A * nat => (fst x, find_code eqA_dec (fst x) c)) (a0, number_of_occurrences eqA_dec a0 (a0 :: l))) []); auto with datatypes.
rewrite <- H1.
apply in_map with (f := fun x : A * nat => (fst x, find_code eqA_dec (fst x) c)).
Admitted.

Theorem restrict_code_pbbuild : forall c : code A, not_null c -> unique_prefix c -> in_alphabet m c -> m <> [] -> permutation (map fst (frequency_list eqA_dec m)) (all_pbleaves (pbbuild empty (restrict_code m c))).
Proof using.
intros c H H0 H1 H2.
rewrite frequency_list_restric_code_map with (c := c).
apply all_pbleaves_pbbuild; auto.
apply restrict_not_null; auto.
Admitted.

Theorem restrict_code_in : forall (a : A) (c : code A), In a m -> find_code eqA_dec a c = find_code eqA_dec a (restrict_code m c).
Proof using.
intros a c H.
apply sym_equal; apply find_code_correct2; auto.
apply restrict_code_unique_key.
generalize (in_frequency_map _ eqA_dec m a H).
unfold restrict_code in |- *; elim (frequency_list eqA_dec m); simpl in |- *; auto with datatypes.
intros a0; case a0; simpl in |- *; auto with datatypes.
intros a1 n l H0 [H1| H1]; try rewrite H1; auto.
