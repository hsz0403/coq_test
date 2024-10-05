Require Import List.
From Huffman Require Import AuxLib.
From Huffman Require Import Code.
From Huffman Require Import Build.
From Huffman Require Import ISort.
Require Import Compare_dec.
From Huffman Require Import Permutation.
From Huffman Require Import UniqueKey.
Section PBTree.
Variable A : Type.
Variable empty : A.
Variable eqA_dec : forall a b : A, {a = b} + {a <> b}.
Inductive pbtree : Type := | pbleaf : A -> pbtree | pbleft : pbtree -> pbtree | pbright : pbtree -> pbtree | pbnode : pbtree -> pbtree -> pbtree.
Inductive inpb : pbtree -> pbtree -> Prop := | inpb_leaf : forall t : pbtree, inpb t t | inpb_left : forall t t1 t2 : pbtree, inpb t t1 -> inpb t (pbleft t1) | inpb_right : forall t t1 t2 : pbtree, inpb t t1 -> inpb t (pbright t1) | inpb_node_l : forall t t1 t2 : pbtree, inpb t t1 -> inpb t (pbnode t1 t2) | inpb_node_r : forall t t1 t2 : pbtree, inpb t t2 -> inpb t (pbnode t1 t2).
Hint Constructors inpb : core.
Definition pbtree_dec : forall a b : pbtree, {a = b} + {a <> b}.
Proof.
intros a; elim a; simpl in |- *; auto.
intros a0 b; case b; try (intros; right; red in |- *; intros; discriminate).
intros a1; case (eqA_dec a0 a1); intros H1.
left; rewrite H1; auto.
right; red in |- *; contradict H1; inversion H1; auto.
intros p H b; case b; try (intros; right; red in |- *; intros; discriminate).
intros p1; case (H p1).
intros e; rewrite e; auto.
intros H1; right; contradict H1; inversion H1; auto.
intros p H b; case b; try (intros; right; red in |- *; intros; discriminate).
intros p1; case (H p1).
intros e; rewrite e; auto.
intros H1; right; contradict H1; inversion H1; auto.
intros p H p0 H0 b; case b; try (intros; right; red in |- *; intros; discriminate).
intros p1 p2; case (H p1); intros H1.
case (H0 p2); intros H2.
left; rewrite H1; rewrite H2; auto.
right; contradict H2; injection H2; auto.
right; contradict H1; injection H1; auto.
Defined.
Definition inpb_dec : forall a b, {inpb a b} + {~ inpb a b}.
Proof.
intros a b; elim b.
intros a0; case a; try (intros; right; red in |- *; intros HH; inversion HH; auto; fail).
intros a1; case (eqA_dec a1 a0); intros HH.
left; rewrite HH; auto.
right; contradict HH; inversion HH; auto.
intros p Hp; case Hp; auto; intros HH.
case (pbtree_dec a (pbleft p)); intros HH1.
left; rewrite HH1; auto.
right; red in |- *; intros HH2; generalize HH HH1; inversion HH2; auto.
intros p Hp; case Hp; auto; intros HH.
case (pbtree_dec a (pbright p)); intros HH1.
left; rewrite HH1; auto.
right; red in |- *; intros HH2; generalize HH HH1; inversion HH2; auto.
intros p H p0 H0.
case H; auto; intros H1.
case H0; auto; intros H2.
case (pbtree_dec a (pbnode p p0)); intros HH1.
left; rewrite HH1; auto.
right; red in |- *; intros HH2; generalize H1 H2 HH1; inversion HH2; auto.
Defined.
Definition distinct_pbleaves (t : pbtree) : Prop := forall t0 t1 t2 : pbtree, inpb (pbnode t1 t2) t -> inpb t0 t1 -> inpb t0 t2 -> False.
Hint Resolve distinct_pbleaves_Leaf : core.
Hint Resolve distinct_pbleaves_pbleaf : core.
Hint Resolve distinct_pbleaves_pbleft distinct_pbleaves_pbright : core.
Fixpoint compute_pbcode (a : pbtree) : code A := match a with | pbleaf b => (b, []) :: [] | pbleft l1 => map (fun v : A * list bool => match v with | (a1, b1) => (a1, false :: b1) end) (compute_pbcode l1) | pbright l1 => map (fun v : A * list bool => match v with | (a1, b1) => (a1, true :: b1) end) (compute_pbcode l1) | pbnode l1 l2 => map (fun v : A * list bool => match v with | (a1, b1) => (a1, false :: b1) end) (compute_pbcode l1) ++ map (fun v : A * list bool => match v with | (a1, b1) => (a1, true :: b1) end) (compute_pbcode l2) end.
Hint Resolve compute_pbcode_not_null : core.
Inductive pbfree : list bool -> pbtree -> Prop := | pbfree_left1 : forall b l, pbfree (true :: l) (pbleft b) | pbfree_left2 : forall b l, pbfree l b -> pbfree (false :: l) (pbleft b) | pbfree_right1 : forall b l, pbfree (false :: l) (pbright b) | pbfree_right2 : forall b l, pbfree l b -> pbfree (true :: l) (pbright b) | pbfree_node1 : forall b c l, pbfree l b -> pbfree (false :: l) (pbnode b c) | pbfree_node2 : forall b c l, pbfree l b -> pbfree (true :: l) (pbnode c b).
Hint Constructors pbfree : core.
Fixpoint pbadd (a : A) (t : pbtree) (l : list bool) {struct l} : pbtree := match l with | [] => pbleaf a | false :: l1 => match t with | pbnode t1 t2 => pbnode (pbadd a t1 l1) t2 | pbleft t1 => pbleft (pbadd a t1 l1) | pbright t2 => pbnode (pbadd a (pbleaf empty) l1) t2 | _ => pbleft (pbadd a (pbleaf empty) l1) end | true :: l1 => match t with | pbnode t1 t2 => pbnode t1 (pbadd a t2 l1) | pbright t2 => pbright (pbadd a t2 l1) | pbleft t1 => pbnode t1 (pbadd a (pbleaf empty) l1) | _ => pbright (pbadd a (pbleaf empty) l1) end end.
Hint Resolve inpb_pbadd : core.
Fixpoint all_pbleaves (t : pbtree) : list A := match t with | pbleaf a => a :: [] | pbleft t1 => all_pbleaves t1 | pbright t1 => all_pbleaves t1 | pbnode t1 t2 => all_pbleaves t1 ++ all_pbleaves t2 end.
Definition pbbuild (l : code A) : pbtree := fold_right (fun a c => pbadd (fst a) c (snd a)) (pbleaf empty) l.
End PBTree.
Arguments pbleaf [A].
Arguments pbleft [A].
Arguments pbright [A].
Arguments pbnode [A].
Arguments inpb [A].
Arguments pbfree [A].
Arguments compute_pbcode [A].
Arguments pbadd [A].
Arguments pbbuild [A].
Arguments all_pbleaves [A].
Arguments distinct_pbleaves [A].
Arguments compute_pbcode [A].
Arguments inpb_dec [A].
Hint Constructors inpb : core.
Hint Resolve distinct_pbleaves_pbleaf : core.
Hint Resolve distinct_pbleaves_pbleft distinct_pbleaves_pbright : core.
Hint Resolve compute_pbcode_not_null : core.
Hint Resolve compute_pbcode_not_null : core.
Hint Constructors pbfree : core.

Theorem pbleaf_or_not : forall p, (exists a, p = pbleaf a) \/ (forall a : A, p <> pbleaf a).
Proof using.
intros p; case p; simpl in |- *; try (intros; right; red in |- *; intros; discriminate).
Admitted.

Definition pbtree_dec : forall a b : pbtree, {a = b} + {a <> b}.
Proof.
intros a; elim a; simpl in |- *; auto.
intros a0 b; case b; try (intros; right; red in |- *; intros; discriminate).
intros a1; case (eqA_dec a0 a1); intros H1.
left; rewrite H1; auto.
right; red in |- *; contradict H1; inversion H1; auto.
intros p H b; case b; try (intros; right; red in |- *; intros; discriminate).
intros p1; case (H p1).
intros e; rewrite e; auto.
intros H1; right; contradict H1; inversion H1; auto.
intros p H b; case b; try (intros; right; red in |- *; intros; discriminate).
intros p1; case (H p1).
intros e; rewrite e; auto.
intros H1; right; contradict H1; inversion H1; auto.
intros p H p0 H0 b; case b; try (intros; right; red in |- *; intros; discriminate).
intros p1 p2; case (H p1); intros H1.
case (H0 p2); intros H2.
left; rewrite H1; rewrite H2; auto.
right; contradict H2; injection H2; auto.
Admitted.

Definition inpb_dec : forall a b, {inpb a b} + {~ inpb a b}.
Proof.
intros a b; elim b.
intros a0; case a; try (intros; right; red in |- *; intros HH; inversion HH; auto; fail).
intros a1; case (eqA_dec a1 a0); intros HH.
left; rewrite HH; auto.
right; contradict HH; inversion HH; auto.
intros p Hp; case Hp; auto; intros HH.
case (pbtree_dec a (pbleft p)); intros HH1.
left; rewrite HH1; auto.
right; red in |- *; intros HH2; generalize HH HH1; inversion HH2; auto.
intros p Hp; case Hp; auto; intros HH.
case (pbtree_dec a (pbright p)); intros HH1.
left; rewrite HH1; auto.
right; red in |- *; intros HH2; generalize HH HH1; inversion HH2; auto.
intros p H p0 H0.
case H; auto; intros H1.
case H0; auto; intros H2.
case (pbtree_dec a (pbnode p p0)); intros HH1.
left; rewrite HH1; auto.
Admitted.

Theorem inpb_trans : forall t1 t2 t3, inpb t1 t2 -> inpb t2 t3 -> inpb t1 t3.
Proof using.
Admitted.

Theorem distinct_pbleaves_Leaf : forall a : A, distinct_pbleaves (pbleaf a).
Proof using.
intros a; red in |- *.
Admitted.

Theorem distinct_pbleaves_l : forall t1 t2 : pbtree, distinct_pbleaves (pbnode t1 t2) -> distinct_pbleaves t1.
Proof using.
intros t1 t2 H; red in |- *.
intros a t0 t3 H0 H1 H2.
Admitted.

Theorem distinct_pbleaves_r : forall t1 t2 : pbtree, distinct_pbleaves (pbnode t1 t2) -> distinct_pbleaves t2.
Proof using.
intros t1 t2 H; red in |- *.
intros a t0 t3 H0 H1 H2.
Admitted.

Theorem distinct_pbleaves_pl : forall t1 : pbtree, distinct_pbleaves (pbleft t1) -> distinct_pbleaves t1.
Proof using.
intros t1 H; red in |- *.
intros a t0 t3 H0 H1 H2.
Admitted.

Theorem distinct_pbleaves_pr : forall t1 : pbtree, distinct_pbleaves (pbright t1) -> distinct_pbleaves t1.
Proof using.
intros t1 H; red in |- *.
intros a t0 t3 H0 H1 H2.
Admitted.

Theorem distinct_pbleaves_pbleaf : forall a : A, distinct_pbleaves (pbleaf a).
Proof using.
intros a; red in |- *.
Admitted.

Theorem distinct_pbleaves_pbleft : forall t, distinct_pbleaves t -> distinct_pbleaves (pbleft t).
Proof using.
intros t H; red in |- *.
intros a t1 t2 H0 H1 H2; apply (H a t1 t2); auto.
Admitted.

Theorem distinct_pbleaves_pbright : forall t, distinct_pbleaves t -> distinct_pbleaves (pbright t).
Proof using.
intros t H; red in |- *.
intros a t1 t2 H0 H1 H2; apply (H a t1 t2); auto.
Admitted.

Theorem compute_pbcode_not_null : forall p, compute_pbcode p <> [].
Proof using.
Admitted.

Theorem in_pbcompute_inpb : forall (t : pbtree) (a : A) (l : list bool), In (a, l) (compute_pbcode t) -> inpb (pbleaf a) t.
Proof using.
intros t; elim t; simpl in |- *; auto.
intros a a0 l [H1| H1]; try (case H1; fail).
injection H1; intros H2 H3; rewrite H3; auto.
intros p H a l H0; apply inpb_left; auto.
case (in_map_inv _ _ _ _ _ H0).
intros (a1, l1) (Ha1, Hl1); apply (H a l1); auto.
injection Hl1; intros HH1 HH2; rewrite HH2; auto.
intros p H a l H0; apply inpb_right; auto.
case (in_map_inv _ _ _ _ _ H0).
intros (a1, l1) (Ha1, Hl1); apply (H a l1); auto.
injection Hl1; intros HH1 HH2; rewrite HH2; auto.
intros h H h0 H0 a l H1.
case in_app_or with (1 := H1); auto; intros H2.
case (in_map_inv _ _ _ _ _ H2).
intros (a1, l1) (Ha1, Hl1); auto.
apply inpb_node_l; apply (H a l1).
injection Hl1; intros Hl2 Hl3; rewrite Hl3; auto.
case (in_map_inv _ _ _ _ _ H2).
intros (a1, l1) (Ha1, Hl1); auto.
apply inpb_node_r; apply (H0 a l1).
Admitted.

Theorem inpb_ex : forall t : pbtree, exists x, inpb (pbleaf x) t.
Proof using.
intros t; elim t; simpl in |- *; auto.
intros a; exists a; auto.
intros b (a, H); exists a; auto.
intros b (a, H); exists a; auto.
intros b (a, H) b0 H0; exists a; auto.
