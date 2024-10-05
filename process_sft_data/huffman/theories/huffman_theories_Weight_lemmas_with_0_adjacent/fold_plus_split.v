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

Theorem fold_plus_split : forall (B : Type) (l : list B) (c : nat) (f : B -> nat), c + fold_left (fun (a : nat) (b : B) => a + f b) l 0 = fold_left (fun (a : nat) (b : B) => a + f b) l c.
Proof using.
intros B l; elim l; simpl in |- *; auto.
intros a l0 H c f.
rewrite <- (H (f a)).
rewrite <- (H (c + f a)).
rewrite plus_assoc_reverse; auto.
