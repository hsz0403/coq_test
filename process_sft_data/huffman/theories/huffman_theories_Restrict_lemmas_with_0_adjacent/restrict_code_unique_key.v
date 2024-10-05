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
intros a l H; apply f_equal2 with (f := cons (A:=A)); auto.
