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

Theorem restrict_code_in : forall (a : A) (c : code A), In a m -> find_code eqA_dec a c = find_code eqA_dec a (restrict_code m c).
Proof using.
intros a c H.
apply sym_equal; apply find_code_correct2; auto.
apply restrict_code_unique_key.
generalize (in_frequency_map _ eqA_dec m a H).
unfold restrict_code in |- *; elim (frequency_list eqA_dec m); simpl in |- *; auto with datatypes.
intros a0; case a0; simpl in |- *; auto with datatypes.
intros a1 n l H0 [H1| H1]; try rewrite H1; auto.
