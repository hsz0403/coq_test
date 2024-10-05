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

Theorem weight_permutation : forall m c1 c2, unique_prefix c1 -> permutation c1 c2 -> weight m c1 = weight m c2.
Proof using.
intros m c1 c2 H H0; unfold weight in |- *.
apply f_equal with (f := length (A:=bool)).
apply encode_permutation; auto.
