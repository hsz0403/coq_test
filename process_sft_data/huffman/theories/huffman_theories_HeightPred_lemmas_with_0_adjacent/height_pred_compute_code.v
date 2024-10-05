From Huffman Require Export AuxLib.
From Huffman Require Export OrderedCover.
From Huffman Require Export WeightTree.
Require Import ArithRing.
From Huffman Require Export Ordered.
From Huffman Require Export Prod2List.
Section HeightPred.
Variable A : Type.
Variable f : A -> nat.
Variable eqA_dec : forall a b : A, {a = b} + {a <> b}.
Inductive height_pred : nat -> list nat -> list (btree A) -> btree A -> Prop := | height_pred_nil : forall (n : nat) (t : btree A), height_pred n (n :: []) (t :: []) t | height_pred_node : forall (n : nat) (ln1 ln2 : list nat) (t1 t2 : btree A) (l1 l2 : list (btree A)), height_pred (S n) ln1 l1 t1 -> height_pred (S n) ln2 l2 t2 -> height_pred n (ln1 ++ ln2) (l1 ++ l2) (node t1 t2).
Hint Resolve height_pred_nil height_pred_node : core.
End HeightPred.
Arguments height_pred [A].
Hint Resolve height_pred_nil height_pred_node : core.

Theorem height_pred_compute_code : forall (n : nat) (t : btree A), height_pred n (map (fun x => length (snd x) + n) (compute_code t)) (map (fun x => leaf (fst x)) (compute_code t)) t.
Proof using.
intros n t; generalize n; elim t; clear t n; simpl in |- *; auto.
intros b H b0 H0 n.
repeat rewrite map_app.
cut (forall (b : bool) l, map (fun x : A * list bool => length (snd x) + n) (map (fun v : A * list bool => let (a1, b1) := v in (a1, b :: b1)) l) = map (fun x : A * list bool => length (snd x) + S n) l); [ intros E1 | idtac ].
cut (forall b l, map (fun x : A * list bool => leaf (fst x)) (map (fun v : A * list bool => let (a1, b1) := v in (a1, b :: b1)) l) = map (fun x : A * list bool => leaf (fst x)) l); [ intros E2 | idtac ].
apply height_pred_node; repeat rewrite E1; repeat rewrite E2; auto.
intros b1 l; elim l; simpl in |- *; auto.
intros a; case a; simpl in |- *; auto.
intros a0 l0 l1 H1; apply f_equal2 with (f := cons (A:=btree A)); auto.
intros b1 l; elim l; simpl in |- *; auto.
intros a; case a; simpl in |- *; auto.
intros a0 l0 l1 H1; apply f_equal2 with (f := cons (A:=nat)); auto.
