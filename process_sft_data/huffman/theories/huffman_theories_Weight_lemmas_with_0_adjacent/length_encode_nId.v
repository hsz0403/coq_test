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

Theorem length_encode_nId : forall a l1 l n, length (encode eqA_dec ((a, l1) :: l) (id_list a n)) = n * length l1.
Proof using.
intros a l1 l n; elim n; simpl in |- *; auto.
intros n0 H; case (eqA_dec a a); auto.
intros e; rewrite app_length; rewrite H; auto.
intros H1; case H1; auto.
