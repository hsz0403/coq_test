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
apply unique_key_map; auto.
