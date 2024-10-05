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

Theorem restrict_code_pbbuild : forall c : code A, not_null c -> unique_prefix c -> in_alphabet m c -> m <> [] -> permutation (map fst (frequency_list eqA_dec m)) (all_pbleaves (pbbuild empty (restrict_code m c))).
Proof using.
intros c H H0 H1 H2.
rewrite frequency_list_restric_code_map with (c := c).
apply all_pbleaves_pbbuild; auto.
apply restrict_not_null; auto.
apply restrict_unique_prefix; auto.
