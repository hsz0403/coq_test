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

Theorem ulist_unique_key : forall (A B : Type) (l : list (A * B)), ulist (map (fst (B:=_)) l) -> unique_key l.
Proof using.
intros AA BB l; elim l; simpl in |- *; auto.
intros a; case a.
intros a0 b l0 H H0; apply unique_key_cons; auto.
intros b0; red in |- *; intros H1; absurd (In a0 (map (fst (B:=_)) l0)); auto.
inversion H0; auto.
change (In (fst (a0, b0)) (map (fst (B:=_)) l0)) in |- *; auto with datatypes.
apply in_map; auto.
apply H; apply ulist_inv with (1 := H0); auto.
