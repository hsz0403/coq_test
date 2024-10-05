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

Theorem fold_plus_permutation : forall (B : Type) (l1 l2 : list B) (c : nat) (f : B -> nat), permutation l1 l2 -> fold_left (fun (a : nat) (b : B) => a + f b) l1 c = fold_left (fun (a : nat) (b : B) => a + f b) l2 c.
Proof using.
intros B l1 l2 c f H; generalize c f; elim H; clear H l1 l2 c f; simpl in |- *; auto.
intros a b L c f; repeat rewrite <- plus_assoc; rewrite (plus_comm (f a)); auto.
intros L1 L2 L3 H H0 H1 H2 c f; apply trans_equal with (1 := H0 c f); auto.
