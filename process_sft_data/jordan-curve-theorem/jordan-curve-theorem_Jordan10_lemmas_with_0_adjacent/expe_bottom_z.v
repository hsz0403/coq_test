Require Export Jordan9.
Open Scope Z_scope.
Definition expe(m:fmap)(z t:dart):= MA0.expo m z t.
Definition betweene(m:fmap)(z v t:dart):= MA0.between m z v t.
Definition Br1(m:fmap)(x x':dart):fmap:= if succ_dec m zero x then if succ_dec m zero x' then B (L (B m zero x) zero (top m zero x) (bottom m zero x)) zero x' else B m zero x else B m zero x'.
Definition double_link(m:fmap)(x x':dart):Prop:= x <> x' /\ expe m x x'.
Inductive list:Set := lam : list | cons : dart->dart->list->list.
Definition emptyl(l:list):Prop:= match l with lam => True | _ => False end.
Fixpoint isin1(l:list)(z:dart){struct l}:Prop:= match l with lam => False | cons x x' l0 => x = z \/ isin1 l0 z end.
Fixpoint isin2(l:list)(z:dart){struct l}:Prop:= match l with lam => False | cons x x' l0 => x' = z \/ isin2 l0 z end.
Fixpoint len(l:list):nat:= match l with lam => 0%nat | cons _ _ l0 => ((len l0) + 1)%nat end.
Definition first(l:list):dart*dart := match l with lam => (nil,nil) | cons x x' _ => (x,x') end.
Definition tail(l:list):list := match l with lam => lam | cons _ _ l0 => l0 end.
Fixpoint last(l:list):dart*dart := match l with lam => (nil,nil) | cons x x' l0 => match l0 with lam => (x, x') | cons _ _ l1 => last l0 end end.
Fixpoint nth(l:list)(k:nat){struct l}:dart*dart := match l with lam => (nil,nil) | cons x x' l0 => match k with 0%nat => (nil,nil) | S 0%nat => (x,x') | S (S k0) => nth l0 (S k0) end end.
Fixpoint double_link_list(m:fmap)(l:list){struct l}:Prop:= match l with lam => True | cons x x' l0 => double_link m x x' /\ double_link_list m l0 end.
Fixpoint Br(m:fmap)(l:list){struct l}:fmap:= match l with lam => m | cons x x' l0 => Br (Br1 m x x') l0 end.
Fixpoint distinct_edge_list (m:fmap)(x:dart)(l:list){struct l}:Prop:= match l with lam => True | cons xs _ l0 => distinct_edge_list m x l0 /\ ~expe m x xs end.
Fixpoint pre_ring0(m:fmap)(l:list){struct l}:Prop:= match l with lam => True | cons x _ l0 => pre_ring0 m l0 /\ distinct_edge_list m x l0 end.
Definition face_adjacent(m:fmap)(x x' xs xs':dart):= let y':= cA m zero x' in let ys:= cA m zero xs in expf m y' ys.
Fixpoint pre_ring1(m:fmap)(l:list){struct l}:Prop:= match l with lam => True | cons x x' l0 => match l0 with lam => True | cons xs xs' l' => pre_ring1 m l0 /\ face_adjacent m x x' xs xs' end end.
Definition pre_ring2(m:fmap)(l:list):Prop:= match l with lam => True | cons x x' l0 => match (last l) with (xs,xs') => face_adjacent m xs xs' x x' end end.
Definition distinct_faces(m:fmap)(x x' xs xs':dart):Prop:= let y := cA m zero x in let ys:= cA m zero xs in ~expf m y ys.
Fixpoint distinct_face_list (m:fmap)(x x':dart)(l:list){struct l}:Prop:= match l with lam => True | cons xs xs' l0 => distinct_face_list m x x' l0 /\ distinct_faces m x x' xs xs' end.
Fixpoint pre_ring3(m:fmap)(l:list){struct l}:Prop:= match l with lam => True | cons x x' l0 => pre_ring3 m l0 /\ distinct_face_list m x x' l0 end.
Definition ring(m:fmap)(l:list):Prop:= ~emptyl l /\ double_link_list m l /\ pre_ring0 m l /\ pre_ring1 m l /\ pre_ring2 m l /\ pre_ring3 m l.

Lemma expe_bottom_z: forall(m:fmap)(z:dart), inv_hmap m -> exd m z -> MA0.expo m (bottom m zero z) z.
Proof.
induction m.
simpl in |- *.
tauto.
simpl in |- *.
intros.
elim (eq_dart_dec d z).
intros.
apply MA0.expo_refl.
rewrite <- a in |- *.
simpl in |- *.
tauto.
intros.
assert (MA0.expo m (bottom m zero z) z).
apply IHm.
tauto.
tauto.
unfold MA0.expo in H1.
elim H1.
clear H1.
intros.
unfold MA0.expo in |- *.
simpl in |- *.
split.
tauto.
elim H2.
clear H2.
intros i Hi.
split with i.
rewrite <- cA0_MA0_Iter in |- *.
rewrite Iter_cA0_I in |- *.
rewrite cA0_MA0_Iter in |- *.
tauto.
simpl in |- *.
tauto.
tauto.
rename d into k.
rename d0 into x.
rename d1 into y.
simpl in |- *.
intros.
unfold prec_L in H.
elim (eq_dim_dec k zero).
intro.
rewrite a in |- *.
elim (eq_dart_dec y (bottom m zero z)).
intros.
set (z0 := bottom m zero z) in |- *.
fold z0 in a0.
set (x0 := bottom m zero x) in |- *.
assert (inv_hmap m).
tauto.
generalize (IHm z H1 H0).
fold z0 in |- *.
intro.
assert (exd m x).
tauto.
generalize (IHm x H1 H3).
fold x0 in |- *.
intro.
assert (MA0.expo1 m z0 z).
generalize (MA0.expo_expo1 m z0 z).
tauto.
assert (MA0.expo1 m x0 x).
generalize (MA0.expo_expo1 m x0 x).
tauto.
rewrite <- a0 in H5.
assert (MA0.expo (L m zero x y) x0 x).
unfold MA0.expo1 in H6.
elim H6.
clear H6.
intros.
elim H7.
intros i Hi.
generalize (nopred_expe_L_i m i zero x y x0).
intros.
unfold expe in H8.
decompose [and] Hi.
clear Hi.
set (m1 := L m zero x y) in |- *.
rewrite <- H10 in |- *.
rewrite cA0_MA0_Iter in H8.
unfold m1 in |- *.
apply H8.
simpl in |- *.
unfold prec_L in |- *.
rewrite a in H.
tauto.
tauto.
unfold x0 in |- *.
apply not_pred_bottom.
tauto.
tauto.
assert (MA0.expo (L m zero x y) y z).
unfold MA0.expo1 in H5.
elim H5.
clear H5.
intros.
elim H8.
clear H8.
intros j Hj.
generalize (nopred_expe_L_i m j zero x y y).
intros.
unfold expe in H8.
decompose [and] Hj.
clear Hj.
set (m1 := L m zero x y) in |- *.
rewrite <- H10 in |- *.
rewrite cA0_MA0_Iter in H8.
unfold m1 in |- *.
apply H8.
simpl in |- *.
unfold prec_L in |- *.
rewrite a in H.
tauto.
tauto.
rewrite a in H.
tauto.
tauto.
assert (MA0.expo (L m zero x y) x y).
unfold MA0.expo in |- *.
split.
simpl in |- *.
tauto.
split with 1%nat.
rewrite <- cA0_MA0_Iter in |- *.
simpl in |- *.
elim (eq_dart_dec x x).
tauto.
tauto.
apply MA0.expo_trans with x.
tauto.
apply MA0.expo_trans with y.
tauto.
tauto.
intro.
assert (MA0.expo m (bottom m zero z) z).
apply IHm.
tauto.
tauto.
set (zO := bottom m zero z) in |- *.
fold zO in H1.
assert (MA0.expo1 m zO z).
generalize (MA0.expo_expo1 m zO z).
tauto.
unfold MA0.expo1 in H2.
elim H2.
clear H2.
intros.
elim H3.
clear H3.
intros i Hi.
decompose [and] Hi.
clear Hi.
rewrite <- H4 in |- *.
generalize (nopred_expe_L_i m i zero x y zO).
intros.
unfold expe in H5.
rewrite cA0_MA0_Iter in H5.
apply H5.
simpl in |- *.
unfold prec_L in |- *.
rewrite a in H.
tauto.
tauto.
unfold zO in |- *.
apply not_pred_bottom.
tauto.
tauto.
intro.
assert (MA0.expo m (bottom m zero z) z).
apply IHm.
tauto.
tauto.
set (zO := bottom m zero z) in |- *.
fold zO in H1.
assert (MA0.expo1 m zO z).
generalize (MA0.expo_expo1 m zO z).
tauto.
unfold MA0.expo1 in H2.
elim H2.
clear H2.
intros.
elim H3.
clear H3.
intros i Hi.
decompose [and] Hi.
clear Hi.
rewrite <- H4 in |- *.
generalize (nopred_expe_L_i m i k x y zO).
intros.
unfold expe in H5.
rewrite cA0_MA0_Iter in H5.
apply H5.
simpl in |- *.
unfold prec_L in |- *.
tauto.
tauto.
unfold zO in |- *.
apply not_pred_bottom.
tauto.
tauto.
