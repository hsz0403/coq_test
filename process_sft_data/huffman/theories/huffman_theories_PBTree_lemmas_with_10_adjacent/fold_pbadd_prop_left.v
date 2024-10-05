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

Theorem inpb_pbadd : forall a1 l1 t1, inpb (pbleaf a1) (pbadd a1 t1 l1).
Proof using.
intros a1 l1; elim l1; simpl in |- *; auto.
intros b; case b; simpl in |- *; auto.
intros l H t1; (case t1; simpl in |- *; auto).
Admitted.

Theorem inpb_pbadd_ex : forall a1 l1 t1 t, inpb t (pbadd a1 t1 l1) -> inpb (pbleaf a1) t \/ inpb t t1.
Proof using.
intros a1 l1; elim l1; simpl in |- *; auto.
intros t1 t H; inversion H; auto.
intros a l H t1 t; case a; case t1; simpl in |- *; auto.
intros a0 H0; inversion H0; auto.
generalize H3 H; case l; simpl in |- *; auto.
intros p H0; inversion H0; auto.
left; generalize H3; elim l; simpl in |- *; auto.
intros HH; inversion HH; auto.
intros b; case b; simpl in |- *; auto.
intros l0 H5 H6; inversion H6; auto.
intros l0 H5 H6; inversion H6; auto.
intros p H0; inversion H0; auto.
case (H p t); auto.
intros p p0 H0; inversion H0; auto.
case (H p0 t); auto.
intros a0 H0; inversion H0; auto.
left; generalize H3; elim l; simpl in |- *; auto.
intros HH; inversion HH; auto.
intros b; case b; simpl in |- *; auto.
intros l0 H5 H6; inversion H6; auto.
intros l0 H5 H6; inversion H6; auto.
intros p H0; inversion H0; auto.
case (H p t); auto.
intros p H0; inversion H0; auto.
left; generalize H3; elim l; simpl in |- *; auto.
intros HH; inversion HH; auto.
intros b; case b; simpl in |- *; auto.
intros l0 H5 H6; inversion H6; auto.
intros l0 H5 H6; inversion H6; auto.
intros p p0 H0; inversion H0; auto.
Admitted.

Theorem all_pbleaves_in : forall t a, inpb (pbleaf a) t -> In a (all_pbleaves t).
Proof using.
intros t; elim t; simpl in |- *; auto.
intros a a0 H; inversion H; auto.
intros p H a H0; inversion H0; auto.
intros p H a H0; inversion H0; auto.
Admitted.

Theorem all_pbleaves_inpb : forall t a, In a (all_pbleaves t) -> inpb (pbleaf a) t.
Proof using.
intros t; elim t; simpl in |- *; auto.
intros a a0 [H| H]; [ rewrite H | case H ]; auto.
Admitted.

Theorem all_pbleaves_unique : forall t, ulist (all_pbleaves t) -> distinct_pbleaves t.
Proof using.
intros t; elim t; simpl in |- *; auto.
intros b H b0 H0 H1; red in |- *.
intros t0 t1 t2 H2; inversion H2.
intros H4 H7; case (inpb_ex t0); intros a HH.
apply ulist_app_inv with (a := a) (1 := H1); auto; apply all_pbleaves_in; apply inpb_trans with (1 := HH); auto.
apply H; auto; try apply ulist_app_inv_l with (1 := H1).
Admitted.

Theorem all_pbleaves_ulist : forall t, distinct_pbleaves t -> ulist (all_pbleaves t).
Proof using.
intros t; elim t; simpl in |- *; auto.
intros p H H0; apply H; apply distinct_pbleaves_pl; auto.
intros p H H0; apply H; apply distinct_pbleaves_pr; auto.
intros b H b0 H0 H1; apply ulist_app; auto.
apply H; apply distinct_pbleaves_l with (1 := H1).
apply H0; apply distinct_pbleaves_r with (1 := H1).
intros a H2 H3; case (H1 (pbleaf a) b b0); auto.
apply all_pbleaves_inpb with (1 := H2).
Admitted.

Theorem all_pbleaves_pbadd : forall l1 a1 a2 l, In a2 (all_pbleaves (pbadd a1 l l1)) -> a2 = a1 \/ In a2 (all_pbleaves l).
Proof using.
intros l1; elim l1; simpl in |- *; auto.
intros a1 a2 l [H| H]; auto; case H.
intros a; case a.
intros l H a1 a2 l0; case l0; simpl in |- *; auto.
intros a0; elim l; simpl in |- *; auto.
intuition.
intros a3; case a3; simpl in |- *; auto.
intros p H0; case in_app_or with (1 := H0); auto.
elim l; simpl in |- *; auto.
intuition.
intros a3; case a3; simpl in |- *; auto.
intros p p0 H0; case in_app_or with (1 := H0); auto with datatypes.
intros H1; case H with (1 := H1); intuition.
intros l H a1 a2 l0; case l0; simpl in |- *; auto.
intros a0; elim l; simpl in |- *; auto.
intuition.
intros a3; case a3; simpl in |- *; auto.
intros p H0; case in_app_or with (1 := H0); auto.
elim l; simpl in |- *; auto.
intuition.
intros a3; case a3; simpl in |- *; auto.
intros p p0 H0; case in_app_or with (1 := H0); auto with datatypes.
Admitted.

Theorem all_pbleaves_pbleaf : forall l a1 a2, all_pbleaves (pbadd a1 (pbleaf a2) l) = a1 :: [].
Proof using.
intros l; elim l; simpl in |- *; auto.
Admitted.

Theorem ulist_pbadd_prop2 : forall a1 l1 t, ~ inpb (pbleaf a1) t -> ulist (all_pbleaves t) -> ulist (all_pbleaves (pbadd a1 t l1)).
Proof using.
intros a1 l1; elim l1; simpl in |- *; auto.
intros b; case b; simpl in |- *; auto.
intros l H t; case t; simpl in |- *; auto.
intros a H0 H1; rewrite all_pbleaves_pbleaf; simpl in |- *; auto.
rewrite all_pbleaves_pbleaf; intros p H0 H1.
apply ulist_app; simpl in |- *; auto.
intros a H2 [H3| H3]; auto; (case H0; rewrite H3); auto.
apply all_pbleaves_inpb; auto.
intros p p0 H0 H1; apply ulist_app; auto.
apply ulist_app_inv_l with (1 := H1); auto.
apply H.
contradict H0; auto.
apply ulist_app_inv_r with (1 := H1); auto.
intros a H2 H3; case all_pbleaves_pbadd with (1 := H3).
intros H4; contradict H0; rewrite <- H4; apply all_pbleaves_inpb; simpl in |- *; auto with datatypes.
intros H4; apply ulist_app_inv with (1 := H1) (a := a); auto.
intros l H t; case t; simpl in |- *; auto.
intros a H0 H1; rewrite all_pbleaves_pbleaf; simpl in |- *; auto.
rewrite all_pbleaves_pbleaf; intros p H0 H1.
apply ulist_app; simpl in |- *; auto.
intros a [H3| H3] H2; auto; (case H0; rewrite H3); auto.
apply all_pbleaves_inpb; auto.
intros p p0 H0 H1; apply ulist_app; auto.
apply H.
contradict H0; auto.
apply ulist_app_inv_l with (1 := H1); auto.
apply ulist_app_inv_r with (1 := H1); auto.
intros a H2 H3; case all_pbleaves_pbadd with (1 := H2).
intros H4; contradict H0; rewrite <- H4; apply all_pbleaves_inpb; simpl in |- *; auto with datatypes.
Admitted.

Theorem distinct_pbleaves_pbadd_prop2 : forall a1 l1 l, ~ inpb (pbleaf a1) l -> distinct_pbleaves l -> distinct_pbleaves (pbadd a1 l l1).
Proof using.
intros a1 l1 l H H0; apply all_pbleaves_unique.
apply ulist_pbadd_prop2; auto.
Admitted.

Theorem fold_pbadd_prop_right : forall l a, l <> [] -> fold_right (fun a (c : pbtree) => pbadd (fst a) c (snd a)) (pbleaf a) (map (fun v => match v with | (a1, b1) => (a1, true :: b1) end) l) = pbright (fold_right (fun a (c : pbtree) => pbadd (fst a) c (snd a)) (pbleaf a) l).
Proof using.
intros l; elim l.
intros a H; elim H; simpl in |- *; auto.
simpl in |- *; intros (a1, l1) l0; case l0.
case l1; simpl in |- *; auto.
intros p l2 H a H0.
rewrite H; auto.
Admitted.

Theorem fold_pbadd_prop_node : forall l a, l <> [] -> fold_right (fun a (c : pbtree) => pbadd (fst a) c (snd a)) (pbright a) (map (fun v => match v with | (a1, b1) => (a1, false :: b1) end) l) = pbnode (fold_right (fun a (c : pbtree) => pbadd (fst a) c (snd a)) (pbleaf empty) l) a.
Proof using.
intros l; elim l.
intros a H; elim H; simpl in |- *; auto.
simpl in |- *; intros (a1, l1) l0; case l0.
case l1; simpl in |- *; auto.
intros p l2 H a H0.
rewrite H; auto.
Admitted.

Theorem pbfree_pbbuild_prop1 : forall a l1 l2, l2 <> [] -> unique_prefix ((a, l1) :: l2) -> pbfree l1 (pbbuild l2).
Proof using.
intros a l1 l2; generalize a l1; elim l2; clear a l1 l2; simpl in |- *; auto.
intros a l1 H; elim H; auto.
intros (a1, l1) l; case l.
unfold pbbuild in |- *; simpl in |- *; intros H a l0 H0 H1; apply pbfree_pbadd_prop1.
red in |- *; intros H2; absurd (a = a1).
red in |- *; intros H3; case unique_key_in with (a := a) (b1 := l0) (b2 := l1) (1 := unique_prefix2 _ _ H1); simpl in |- *; auto.
rewrite H3; auto.
apply unique_prefix1 with (1 := H1) (lb1 := l0) (lb2 := l1); simpl in |- *; auto.
red in |- *; intros H2; absurd (a = a1).
red in |- *; intros H3; case unique_key_in with (a := a) (b1 := l0) (b2 := l1) (1 := unique_prefix2 _ _ H1); simpl in |- *; auto.
rewrite H3; auto.
apply sym_equal; apply unique_prefix1 with (1 := H1) (lb1 := l1) (lb2 := l0); simpl in |- *; auto.
intros p l0 H a l2 H0 H1.
unfold pbbuild in |- *; simpl in |- *.
apply pbfree_pbadd_prop2; auto.
apply H with (a := a).
red in |- *; intros; discriminate.
apply unique_prefix_inv with (a := a1) (l := l1).
apply unique_prefix_permutation with (2 := H1); auto.
red in |- *; intros H2; absurd (a = a1).
red in |- *; intros H3; case unique_key_in with (a := a) (b1 := l2) (b2 := l1) (1 := unique_prefix2 _ _ H1); simpl in |- *; auto.
rewrite H3; auto.
apply sym_equal; apply unique_prefix1 with (1 := H1) (lb1 := l1) (lb2 := l2); simpl in |- *; auto.
red in |- *; intros H2; absurd (a = a1).
red in |- *; intros H3; case unique_key_in with (a := a) (b1 := l2) (b2 := l1) (1 := unique_prefix2 _ _ H1); simpl in |- *; auto.
rewrite H3; auto.
Admitted.

Theorem all_pbleaves_compute_pb : forall t, permutation (map (fst (B:=_)) (compute_pbcode t)) (all_pbleaves t).
Proof using.
cut (forall b l, map (fst (B:=_)) (map (fun v : A * list bool => let (a1, b1) := v in (a1, b :: b1)) l) = map (fst (B:=_)) l); [ intros HH | idtac ].
intros t; elim t; simpl in |- *; auto.
intros p H; rewrite HH; auto.
intros p H; rewrite HH; auto.
intros p H p0 H0; rewrite map_app; apply permutation_app_comp; auto.
repeat rewrite HH; auto.
repeat rewrite HH; auto.
intros b l; elim l; simpl in |- *; auto.
intros a l0 H1; apply f_equal2 with (f := cons (A:=A)); auto.
Admitted.

Theorem pbbuild_compute_perm : forall c, c <> [] -> unique_prefix c -> permutation (compute_pbcode (pbbuild c)) c.
Proof using.
intros c; elim c; simpl in |- *; auto.
intros H; case H; auto.
intros (a1, l1) l.
case l.
unfold pbbuild in |- *; simpl in |- *; auto.
intros H H0 H1; rewrite pbadd_prop1; auto.
intros (a2, l2) l3; simpl in |- *.
intros H H0 H1; apply permutation_trans with ((a1, l1) :: compute_pbcode (pbadd a2 (pbbuild l3) l2)).
unfold pbbuild in |- *; simpl in |- *; apply pbadd_prop2.
cut (~ is_prefix l1 l2); [ intros Ip1 | idtac ].
cut (~ is_prefix l2 l1); [ intros Ip2 | idtac ].
generalize H1; case l3; auto.
intros H2; apply pbfree_pbadd_prop1; auto.
intros p l0 H2.
apply pbfree_pbadd_prop2; auto.
change (pbfree l1 (pbbuild (p :: l0))) in |- *.
apply pbfree_pbbuild_prop1 with (a := a1); auto.
red in |- *; intros; discriminate.
apply unique_prefix_inv with (a := a2) (l := l2).
apply unique_prefix_permutation with (2 := H2); auto.
red in |- *; intros HH2; absurd (a1 = a2).
red in |- *; intros H3; case unique_key_in with (a := a1) (b1 := l1) (b2 := l2) (1 := unique_prefix2 _ _ H1); simpl in |- *; auto.
rewrite H3; auto.
apply sym_equal; apply unique_prefix1 with (1 := H1) (lb1 := l2) (lb2 := l1); simpl in |- *; auto.
red in |- *; intros HH2; absurd (a1 = a2).
red in |- *; intros H3; case unique_key_in with (a := a1) (b1 := l1) (b2 := l2) (1 := unique_prefix2 _ _ H1); simpl in |- *; auto.
rewrite H3; auto.
apply unique_prefix1 with (1 := H1) (lb1 := l1) (lb2 := l2); simpl in |- *; auto.
apply permutation_skip.
apply H; auto.
red in |- *; intros Hj; discriminate.
Admitted.

Theorem all_pbleaves_pbbuild : forall c, c <> [] -> unique_prefix c -> permutation (map (fst (B:=_)) c) (all_pbleaves (pbbuild c)).
Proof using.
intros c H H0; apply permutation_trans with (map (fst (B:=_)) (compute_pbcode (pbbuild c))).
apply permutation_map.
apply permutation_sym; apply pbbuild_compute_perm; auto.
Admitted.

Theorem inpb_pbbuild_inv : forall a c, c <> [] -> inpb (pbleaf a) (pbbuild c) -> exists l, In (a, l) c.
Proof using.
intros a c; generalize a; elim c; simpl in |- *; auto.
intros a0 H; elim H; auto.
intros (a1, l1).
intros l; case l.
simpl in |- *; auto.
unfold pbbuild in |- *; simpl in |- *; intros H a0 H0 H1; exists l1; left; apply f_equal2 with (f := pair (A:=A) (B:=list bool)); auto.
apply sym_equal; apply inpbleaf_eq with (1 := H1).
unfold pbbuild in |- *; simpl in |- *; intros p l0 H a0 H0 H1.
case inpbleaf_pbadd_inv with (1 := H1); auto; intros H2.
exists l1; left; apply f_equal2 with (f := pair (A:=A) (B:=list bool)); auto.
case (H a0); auto.
red in |- *; intros H3; discriminate.
Admitted.

Theorem pbbuild_distinct_pbleaves : forall c, unique_prefix c -> distinct_pbleaves (pbbuild c).
Proof using.
intros c; elim c; unfold pbbuild in |- *; simpl in |- *; auto.
intros (a1, l1) l; case l; auto.
simpl in |- *; intros H H0; apply distinct_pbleaves_pbadd_prop1; auto.
intros (a2, l2) l3 H0 H1; apply distinct_pbleaves_pbadd_prop2; auto.
change (~ inpb (pbleaf a1) (pbbuild ((a2, l2) :: l3))) in |- *.
red in |- *; intros H2; case inpb_pbbuild_inv with (2 := H2).
red in |- *; intros H; discriminate.
intros x H; case unique_key_in with (b2 := x) (1 := unique_prefix2 _ _ H1); auto.
apply H0.
Admitted.

Theorem pbbuild_compute_peq : forall t, distinct_pbleaves t -> pbbuild (compute_pbcode t) = t.
Proof using.
intros t; elim t; simpl in |- *; auto.
intros p H H0; unfold pbbuild in |- *.
rewrite fold_pbadd_prop_left; auto.
change (pbleft (pbbuild (compute_pbcode p)) = pbleft p) in |- *.
apply f_equal with (f := pbleft); auto; apply H.
apply distinct_pbleaves_pl with (1 := H0).
intros p H H0; unfold pbbuild in |- *.
rewrite fold_pbadd_prop_right; auto.
change (pbright (pbbuild (compute_pbcode p)) = pbright p) in |- *.
apply f_equal with (f := pbright); auto; apply H.
apply distinct_pbleaves_pr with (1 := H0).
intros p H p0 H0 H1.
unfold pbbuild in |- *.
rewrite fold_right_app.
rewrite fold_pbadd_prop_right; auto.
rewrite fold_pbadd_prop_node; auto.
change (pbnode (pbbuild (compute_pbcode p)) (pbbuild (compute_pbcode p0)) = pbnode p p0) in |- *.
apply f_equal2 with (f := pbnode).
apply H; apply distinct_pbleaves_l with (1 := H1).
Admitted.

Theorem pbbuild_true_pbright : forall c, c <> [] -> pbbuild (map (fun x => (fst x, true :: snd x)) c) = pbright (pbbuild c).
Proof using.
intros c; elim c; simpl in |- *; auto.
intros H; case H; auto.
intros a l; case a; case l.
intros a0 l0 H H0; simpl in |- *; auto.
intros p l0 a0 l1 H H0; rewrite H; auto.
Admitted.

Theorem fold_pbadd_prop_left : forall l a, l <> [] -> fold_right (fun a (c : pbtree) => pbadd (fst a) c (snd a)) (pbleaf a) (map (fun v => match v with | (a1, b1) => (a1, false :: b1) end) l) = pbleft (fold_right (fun a (c : pbtree) => pbadd (fst a) c (snd a)) (pbleaf a) l).
Proof using.
intros l; elim l.
intros a H; elim H; simpl in |- *; auto.
simpl in |- *; intros (a1, l1) l0; case l0.
case l1; simpl in |- *; auto.
intros p l2 H a H0.
rewrite H; auto.
red in |- *; intros H1; discriminate.
