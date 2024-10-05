From Huffman Require Export AuxLib.
From Huffman Require Export Code.
From Huffman Require Export Build.
From Huffman Require Export ISort.
Require Export Compare_dec.
From Huffman Require Export Permutation.
From Huffman Require Export UniqueKey.
From Huffman Require Export PBTree.
From Huffman Require Export BTree.
Section PBTREE2BTREE.
Variable A : Type.
Variable eqA_dec : forall a b : A, {a = b} + {a <> b}.
Variable empty : A.
Fixpoint to_btree (a : pbtree A) : btree A := match a with | pbleaf b => leaf b | pbleft l1 => to_btree l1 | pbright l1 => to_btree l1 | pbnode l1 l2 => node (to_btree l1) (to_btree l2) end.
End PBTREE2BTREE.
Arguments to_btree [A].

Theorem to_btree_inpb : forall a b, inb (leaf a) (to_btree b) -> inpb (pbleaf a) b.
Proof using.
intros a b; generalize a; elim b; clear a b; simpl in |- *; auto.
intros a a0 H; inversion H; auto.
intros p H p0 H0 a H1.
inversion H1; auto.
