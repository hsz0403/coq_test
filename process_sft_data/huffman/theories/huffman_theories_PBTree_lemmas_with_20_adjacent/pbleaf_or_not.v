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

Theorem inpb_ex : forall t : pbtree, exists x, inpb (pbleaf x) t.
Proof using.
intros t; elim t; simpl in |- *; auto.
intros a; exists a; auto.
intros b (a, H); exists a; auto.
intros b (a, H); exists a; auto.
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

Theorem inpb_compute_ex : forall a p, inpb (pbleaf a) p -> exists l, In (a, l) (compute_pbcode p).
Proof using.
intros a p; elim p; simpl in |- *; auto.
intros a0 H; inversion H.
exists []; auto.
intros p0 H H0; case H; auto.
inversion H0; auto.
intros x1; elim (compute_pbcode p0); simpl in |- *; auto.
intros HH; case HH.
intros a0 l H1 [H2| H2]; auto.
exists (false :: x1); left; rewrite H2; auto.
case H1; auto.
intros x H3; exists x; auto.
intros p0 H H0; case H; auto.
inversion H0; auto.
intros x1; elim (compute_pbcode p0); simpl in |- *; auto.
intros HH; case HH.
intros a0 l H1 [H2| H2]; auto.
exists (true :: x1); left; rewrite H2; auto.
case H1; auto.
intros x H3; exists x; auto.
intros p0 H p1 H0 H1; inversion H1.
case H; auto.
intros x Hx; exists (false :: x).
apply in_or_app; left; auto.
change (In ((fun v => match v with | (a1, b1) => (a1, false :: b1) end) (a, x)) (map (fun v => match v with | (a1, b1) => (a1, false :: b1) end) (compute_pbcode p0))) in |- *; apply in_map; auto.
case H0; auto.
intros x Hx; exists (true :: x).
apply in_or_app; right; auto.
Admitted.

Theorem pb_unique_prefix1 : forall (t : pbtree) (a1 a2 : A) (lb1 lb2 : list bool), In (a1, lb1) (compute_pbcode t) -> In (a2, lb2) (compute_pbcode t) -> is_prefix lb1 lb2 -> a1 = a2 :>A.
Proof using.
intros t; elim t; simpl in |- *; auto.
intros leaf a1 a2 lb1 lb2 H1 H2.
case H1; intros H3; [ injection H3 | case H3 ].
case H2; intros H4; [ injection H4 | case H4 ].
intros H H0 H5 H6 H7; apply trans_equal with (2 := H0); auto.
intros p H a1 a2 lb1 lb2 H0 H1 H2.
case (in_map_inv _ _ _ _ _ H0).
intros (a3, l3) (Ha3, Hl3).
case (in_map_inv _ _ _ _ _ H1).
intros (a4, l4) (Ha4, Hl4).
apply (H a1 a2 l3 l4); auto.
injection Hl3; intros HH1 HH2; rewrite HH2; auto.
injection Hl4; intros HH1 HH2; rewrite HH2; auto.
cut (is_prefix (false :: l3) (false :: l4)); [ intros HH1; inversion HH1; auto | idtac ].
injection Hl3; injection Hl4; intros HH1 HH2 HH3 HH4; rewrite <- HH3; rewrite <- HH1; auto.
intros p H a1 a2 lb1 lb2 H0 H1 H2.
case (in_map_inv _ _ _ _ _ H0).
intros (a3, l3) (Ha3, Hl3).
case (in_map_inv _ _ _ _ _ H1).
intros (a4, l4) (Ha4, Hl4).
apply (H a1 a2 l3 l4); auto.
injection Hl3; intros HH1 HH2; rewrite HH2; auto.
injection Hl4; intros HH1 HH2; rewrite HH2; auto.
cut (is_prefix (true :: l3) (true :: l4)); [ intros HH1; inversion HH1; auto | idtac ].
injection Hl3; injection Hl4; intros HH1 HH2 HH3 HH4; rewrite <- HH3; rewrite <- HH1; auto.
intros t1 Rec1 t2 Rec2 a1 a2 lb1 lb2 H1 H2.
case (in_app_or _ _ _ H1); case (in_app_or _ _ _ H2); clear H1 H2; intros H2 H1 H3.
generalize H1 H2; inversion H3.
intros H4; case (in_map_inv _ _ _ _ _ H4).
intros x; case x; intros x1 x2 (H5, H6); discriminate.
intros H5 H6; apply Rec1 with (lb1 := l1) (lb2 := l2); auto.
case (in_map_inv _ _ _ _ _ H5).
intros x; case x.
intros a l (H7, H8); injection H8.
intros R1 R2 R3; rewrite R1; rewrite R3; auto.
case (in_map_inv _ _ _ _ _ H6).
intros x; case x.
intros a l (H7, H8); injection H8.
intros R1 R2 R3; rewrite R1; rewrite R3; auto.
generalize H3.
case (in_map_inv _ _ _ _ _ H1).
intros x; case x; intros aa1 ll1 (H4, H5).
case (in_map_inv _ _ _ _ _ H2).
intros x1; case x1; intros aa2 ll2 (H6, H7).
inversion H5; inversion H7; intros tH8; inversion tH8.
generalize H3.
case (in_map_inv _ _ _ _ _ H1).
intros x; case x; intros aa1 ll1 (H4, H5).
case (in_map_inv _ _ _ _ _ H2).
intros x1; case x1; intros aa2 ll2 (H6, H7).
inversion H5; inversion H7; intros tH8; inversion tH8.
generalize H1 H2; inversion H3.
intros H4; case (in_map_inv _ _ _ _ _ H4).
intros x; case x; intros x1 x2 (H5, H6); discriminate.
intros H5 H6; apply Rec2 with (lb1 := l1) (lb2 := l2); auto.
case (in_map_inv _ _ _ _ _ H5).
intros x; case x.
intros a l (H7, H8); injection H8.
intros R1 R2 R3; rewrite R1; rewrite R3; auto.
case (in_map_inv _ _ _ _ _ H6).
intros x; case x.
intros a l (H7, H8); injection H8.
Admitted.

Theorem pb_unique_key : forall t, distinct_pbleaves t -> unique_key (compute_pbcode t).
Proof using.
intros t; elim t; simpl in |- *; auto.
intros p H H0.
apply unique_key_map; auto.
apply H; apply distinct_pbleaves_pl; auto.
intros (a1, b1) (a2, b2); simpl in |- *; auto.
intros p H H0.
apply unique_key_map; auto.
apply H; apply distinct_pbleaves_pr; auto.
intros (a1, b1) (a2, b2); simpl in |- *; auto.
intros p H p0 H0 H1.
apply unique_key_app; auto.
apply unique_key_map; auto.
apply H; apply distinct_pbleaves_l with (1 := H1); auto.
intros (a1, b1) (a2, b2); simpl in |- *; auto.
apply unique_key_map; auto.
apply H0; apply distinct_pbleaves_r with (1 := H1); auto.
intros (a1, b1) (a2, b2); simpl in |- *; auto.
intros a b1 c H2 H3.
case in_map_inv with (1 := H2); auto; case in_map_inv with (1 := H3); auto.
intros (a1, l1) (Ha1, Hl1) (a2, l2) (Ha2, Hl2).
apply (H1 (pbleaf a) p p0); auto.
injection Hl2; intros HH1 HH2; rewrite HH2.
apply in_pbcompute_inpb with (1 := Ha2).
injection Hl1; intros HH1 HH2; rewrite HH2.
Admitted.

Theorem pb_unique_prefix : forall t : pbtree, distinct_pbleaves t -> unique_prefix (compute_pbcode t).
Proof using.
Admitted.

Theorem pbadd_prop1 : forall a1 a2 l1, compute_pbcode (pbadd a1 (pbleaf a2) l1) = (a1, l1) :: [].
Proof using.
intros a1 a2 l1; generalize a1 a2; elim l1; simpl in |- *; auto; clear a1 a2 l1.
intros a; case a; simpl in |- *; auto.
intros l H a1 a2; rewrite H; simpl in |- *; auto.
Admitted.

Theorem pbadd_prop2 : forall a1 l1 l2, pbfree l1 l2 -> permutation (compute_pbcode (pbadd a1 l2 l1)) ((a1, l1) :: compute_pbcode l2).
Proof using.
intros a1 l1 l2 H; generalize a1; elim H; clear H a1 l1 l2; simpl in |- *; auto.
intros b l a1; rewrite pbadd_prop1; simpl in |- *; auto.
apply permutation_trans with (((a1, true :: l) :: []) ++ map (fun v => match v with | (a0, b1) => (a0, false :: b1) end) (compute_pbcode b)); auto.
simpl in |- *; auto.
intros b l H H0 a1.
apply permutation_trans with (map (fun v => match v with | (a0, b1) => (a0, false :: b1) end) ((a1, l) :: compute_pbcode b)); auto.
intros b l a1; rewrite pbadd_prop1; simpl in |- *; auto.
intros b l H H0 a1.
apply permutation_trans with (map (fun v => match v with | (a0, b1) => (a0, true :: b1) end) ((a1, l) :: compute_pbcode b)); auto.
intros b c l H H0 a1.
apply permutation_trans with (map (fun v => match v with | (a0, b1) => (a0, false :: b1) end) ((a1, l) :: compute_pbcode b) ++ map (fun v => match v with | (a0, b1) => (a0, true :: b1) end) (compute_pbcode c)); auto.
intros b c l H H0 a1.
apply permutation_trans with (map (fun v => match v with | (a0, b1) => (a0, false :: b1) end) (compute_pbcode c) ++ map (fun v => match v with | (a0, b1) => (a0, true :: b1) end) ((a1, l) :: compute_pbcode b)); auto.
Admitted.

Theorem pbleaf_or_not : forall p, (exists a, p = pbleaf a) \/ (forall a : A, p <> pbleaf a).
Proof using.
intros p; case p; simpl in |- *; try (intros; right; red in |- *; intros; discriminate).
intros a; left; exists a; simpl in |- *; auto.
