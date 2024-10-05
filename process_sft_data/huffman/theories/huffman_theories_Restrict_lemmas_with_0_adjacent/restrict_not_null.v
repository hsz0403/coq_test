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

Theorem restrict_not_null : forall c, m <> [] -> restrict_code m c <> [].
Proof using.
case m; simpl in |- *; auto.
unfold restrict_code in |- *.
intros a0 l c H H1.
absurd (In ((fun x : A * nat => (fst x, find_code eqA_dec (fst x) c)) (a0, number_of_occurrences eqA_dec a0 (a0 :: l))) []); auto with datatypes.
rewrite <- H1.
apply in_map with (f := fun x : A * nat => (fst x, find_code eqA_dec (fst x) c)).
apply frequency_number_of_occurrences; auto with datatypes.
