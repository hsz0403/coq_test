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
Admitted.

Lemma bottom_bottom_expe: forall(m:fmap)(z t:dart), inv_hmap m -> exd m z -> exd m t -> bottom m zero z = bottom m zero t -> MA0.expo m z t.
Proof.
intros.
apply MA0.expo_trans with (bottom m zero z).
apply MA0.expo_symm.
tauto.
apply expe_bottom_z.
tauto.
tauto.
rewrite H2 in |- *.
apply expe_bottom_z.
tauto.
Admitted.

Lemma top_top_expe: forall(m:fmap)(z t:dart), inv_hmap m -> exd m z -> exd m t -> top m zero z = top m zero t -> MA0.expo m z t.
Proof.
intros.
generalize (cA_top m zero z H H0).
intro.
generalize (cA_top m zero t H H1).
intro.
rewrite H2 in H3.
rewrite H3 in H4.
apply bottom_bottom_expe.
tauto.
tauto.
tauto.
Admitted.

Lemma between_bottom_B0_bis: forall(m:fmap)(x' x:dart), inv_hmap m -> exd m x -> exd m x' -> x' <> x -> let x0 := bottom m zero x in let m0 := B m zero x' in ((betweene m x0 x' x -> bottom m0 zero x = A m zero x') /\ (~betweene m x0 x' x -> bottom m0 zero x = bottom m zero x)).
Proof.
intros.
unfold betweene in |- *.
unfold MA0.between in |- *.
split.
intros.
assert (exd m x0).
unfold x0 in |- *.
apply exd_bottom.
tauto.
tauto.
generalize (H3 H H4).
clear H3.
intro.
elim H3.
intros i Hi.
clear H3.
elim Hi.
clear Hi.
intros j Hj.
decompose [and] Hj.
clear Hj.
assert (~ pred m zero x0).
unfold x0 in |- *.
apply not_pred_bottom.
tauto.
elim (eq_nat_dec i j).
intro.
rewrite a in H3.
rewrite H3 in H6.
tauto.
intro.
unfold m0 in |- *.
rewrite <- H3.
rewrite <- H6.
apply bottom_B0_bis.
tauto.
tauto.
tauto.
omega.
intros.
assert (exd m x0).
unfold x0 in |- *.
apply exd_bottom.
tauto.
tauto.
unfold m0 in |- *.
generalize (not_between_B0 m x' x H H1 H0 H2).
simpl in |- *.
fold x0 in |- *.
intros.
assert (~ MA0.expo m x0 x' \/ (forall i j : nat, x' = Iter (MA0.f m) i x0 -> x = Iter (MA0.f m) j x0 -> (i < MA0.Iter_upb m x0)%nat -> (j < MA0.Iter_upb m x0)%nat -> (j <= i)%nat)).
apply H5.
unfold betweene in |- *.
unfold MA0.between in |- *.
tauto.
clear H5.
elim H6.
clear H6.
intro.
assert (MA0.expo m x0 x).
unfold x0 in |- *.
apply expe_bottom_z.
tauto.
tauto.
assert (MA0.expo1 m x0 x).
generalize (MA0.expo_expo1 m x0 x).
tauto.
unfold MA0.expo1 in H7.
elim H7.
clear H7.
intros.
elim H8.
intros j Hj.
clear H8.
decompose [and] Hj.
clear Hj.
unfold x0 in |- *.
rewrite <- H9.
apply bottom_B0_quad.
tauto.
tauto.
unfold x0 in |- *.
apply not_pred_bottom.
tauto.
tauto.
tauto.
clear H6.
intros.
clear H3.
assert (MA0.expo m x0 x).
unfold x0 in |- *.
apply expe_bottom_z.
tauto.
tauto.
assert (MA0.expo1 m x0 x).
generalize (MA0.expo_expo1 m x0 x).
tauto.
unfold MA0.expo1 in H6.
decompose [and] H6.
clear H6.
elim H8.
clear H8.
intros j Hj.
elim (MA0.expo_dec m x0 x').
intro.
assert (MA0.expo1 m x0 x').
generalize (MA0.expo_expo1 m x0 x').
tauto.
unfold MA0.expo1 in H6.
decompose [and] H6.
clear H6.
elim H9.
clear H9.
intros i Hi.
unfold x0 in |- *.
decompose [and] Hj.
clear Hj.
decompose [and] Hi.
clear Hi.
rewrite <- H9.
rewrite <- H11.
apply bottom_B0_ter.
tauto.
tauto.
unfold x0 in |- *.
apply not_pred_bottom.
tauto.
assert (j <= i)%nat.
apply H5.
symmetry in |- *.
tauto.
symmetry in |- *.
tauto.
tauto.
tauto.
omega.
intro.
decompose [and] Hj.
clear Hj.
rewrite <- H8.
assert (x0 = bottom m zero x0).
unfold x0 in |- *.
rewrite bottom_bottom.
tauto.
tauto.
rewrite H8.
unfold x0 in |- *.
rewrite <- H8.
apply bottom_B0_quad.
tauto.
tauto.
unfold x0 in |- *.
apply not_pred_bottom.
tauto.
tauto.
tauto.
Admitted.

Lemma not_expe_bottom_B0: forall(m:fmap)(x' x:dart), inv_hmap m -> exd m x -> exd m x' -> let m0 := B m zero x' in ~ expe m x' x -> bottom m0 zero x = bottom m zero x.
Proof.
unfold expe in |- *.
intros.
set (x0 := bottom m zero x) in |- *.
assert (~ betweene m x0 x' x).
intro.
unfold betweene in H3.
assert (exd m x0).
unfold x0 in |- *.
apply exd_bottom.
tauto.
tauto.
generalize (MA0.between_expo m x0 x' x H H4 H3).
intros.
absurd (MA0.expo m x' x).
tauto.
apply MA0.expo_trans with x0.
apply MA0.expo_symm.
tauto.
tauto.
tauto.
fold x0 in |- *.
assert (x' <> x).
intro.
rewrite H4 in H2.
elim H2.
apply MA0.expo_refl.
tauto.
generalize (between_bottom_B0_bis m x' x H H0 H1 H4).
simpl in |- *.
fold x0 in |- *.
Admitted.

Lemma existi_dec:forall(m:fmap)(z v:dart)(k:nat), (exists i:nat, (i < k)%nat /\ Iter (MA0.f m) i z = v) \/ (~exists i:nat, (i < k)%nat /\ Iter (MA0.f m) i z = v).
Proof.
induction k.
right.
intro.
elim H.
intros.
omega.
elim IHk.
clear IHk.
intro.
elim H.
clear H.
intros i Hi.
left.
split with i.
split.
omega.
tauto.
clear IHk.
intro.
elim (eq_dart_dec (Iter (MA0.f m) k z) v).
intro.
left.
split with k.
split.
omega.
tauto.
intro.
right.
intro.
elim H0.
intros i Hi.
apply H.
split with i.
elim (eq_nat_dec i k).
intro.
rewrite a in Hi.
tauto.
intro.
split.
omega.
Admitted.

Lemma MA0_between_dec: forall(m:fmap)(z v t:dart), inv_hmap m -> exd m z -> (MA0.between m z v t \/ ~MA0.between m z v t).
Proof.
intros.
set (p := MA0.Iter_upb m z) in |- *.
generalize (existi_dec m z v p).
generalize (existi_dec m z t p).
intros.
elim H1.
elim H2.
clear H1 H2.
intros.
elim H1.
intros i Hi.
clear H1.
elim H2.
intros j Hj.
clear H2.
decompose [and] Hi.
clear Hi.
intros.
decompose [and] Hj.
clear Hj.
intros.
elim (le_lt_dec i j).
intro.
left.
unfold MA0.between in |- *.
split with i.
split with j.
tauto.
intro.
right.
unfold MA0.between in |- *.
intro.
elim H5.
intros i0 Hi.
clear H5.
elim Hi.
clear Hi.
intros j0 Hj0.
decompose [and] Hj0.
clear Hj0.
fold p in H9.
assert (i = i0).
apply (MA0.unicity_mod_p m z i i0).
tauto.
tauto.
fold p in |- *.
tauto.
fold p in |- *.
omega.
rewrite H5 in |- *.
tauto.
assert (j = j0).
apply (MA0.unicity_mod_p m z j j0).
tauto.
tauto.
fold p in |- *.
tauto.
fold p in |- *.
omega.
rewrite H7 in |- *.
tauto.
rewrite H8 in b.
rewrite H10 in b.
omega.
tauto.
tauto.
clear H2.
clear H1.
intros.
right.
unfold MA0.between in |- *.
intro.
elim H3.
intros i Hi.
clear H3.
elim Hi.
clear Hi.
intros j Hj.
fold p in Hj.
apply H1.
split with i.
split.
omega.
tauto.
tauto.
tauto.
clear H1.
clear H2.
right.
unfold MA0.between in |- *.
intro.
elim H2.
intros i Hi.
clear H2.
elim Hi.
clear Hi.
intros j Hj.
fold p in Hj.
apply H1.
split with j.
tauto.
tauto.
Admitted.

Lemma betweene_bottom_x_top: forall(m:fmap)(x:dart), inv_hmap m -> succ m zero x -> betweene m (bottom m zero x) x (top m zero x).
Proof.
unfold betweene in |- *.
unfold MA0.between in |- *.
intros.
assert (exd m x).
apply succ_exd with zero.
tauto.
tauto.
generalize (expe_bottom_z m x H H3).
intro.
assert (MA0.expo1 m (bottom m zero x) x).
generalize (MA0.expo_expo1 m (bottom m zero x) x).
tauto.
unfold MA0.expo1 in H5.
elim H5.
clear H5.
intros.
elim H6.
clear H6.
intros i Hi.
split with i.
generalize (MA0.upb_pos m (bottom m zero x) H5).
intro.
set (p := MA0.Iter_upb m (bottom m zero x)) in |- *.
fold p in H6.
fold p in Hi.
split with (p - 1)%nat.
split.
tauto.
split.
rewrite <- cA_1_bottom in |- *.
assert (cA_1 m zero (bottom m zero x) = MA0.f_1 m (bottom m zero x)).
tauto.
rewrite H7 in |- *.
rewrite <- MA0.Iter_f_f_1 in |- *.
simpl in |- *.
unfold p in |- *.
rewrite MA0.Iter_upb_period in |- *.
tauto.
tauto.
tauto.
tauto.
tauto.
omega.
tauto.
tauto.
Admitted.

Lemma cA_L_B_top_bot:forall(m:fmap)(k:dim)(x z:dart), inv_hmap m -> succ m k x -> cA (L (B m k x) k (top m k x) (bottom m k x)) k z = cA m k z.
Proof.
induction k.
simpl in |- *.
intros.
elim (eq_dart_dec (top m zero x) z).
intro.
rewrite <- a in |- *.
rewrite cA_top in |- *.
tauto.
tauto.
apply succ_exd with zero.
tauto.
tauto.
elim (eq_dart_dec (cA_1 (B m zero x) zero (bottom m zero x)) z).
intros.
generalize a.
clear a.
rewrite cA_B in |- *.
rewrite cA_1_B in |- *.
elim (eq_dart_dec (A m zero x) (bottom m zero x)).
intro.
symmetry in a.
absurd (bottom m zero x = A m zero x).
apply succ_bottom.
tauto.
tauto.
tauto.
elim (eq_dart_dec (bottom m zero x) (bottom m zero x)).
elim (eq_dart_dec x (top m zero x)).
intros.
rewrite <- a in b.
tauto.
elim (eq_dart_dec (top m zero x) (top m zero x)).
rewrite cA_eq in |- *.
elim (succ_dec m zero z).
intros.
rewrite a2 in |- *.
tauto.
intros.
rewrite a1 in H0.
tauto.
tauto.
tauto.
tauto.
tauto.
tauto.
tauto.
tauto.
intros.
rewrite cA_B in |- *.
elim (eq_dart_dec x z).
intros.
rewrite cA_eq in |- *.
elim (succ_dec m zero z).
intro.
generalize b.
rewrite cA_1_B in |- *.
elim (eq_dart_dec (A m zero x) (bottom m zero x)).
intro.
symmetry in a1.
absurd (bottom m zero x = A m zero x).
apply succ_bottom.
tauto.
tauto.
tauto.
elim (eq_dart_dec (bottom m zero x) (bottom m zero x)).
intros.
tauto.
tauto.
tauto.
tauto.
rewrite a in |- *.
tauto.
tauto.
elim (eq_dart_dec (top m zero x) z).
tauto.
tauto.
tauto.
tauto.
intros.
assert (exd m x).
apply succ_exd with one.
tauto.
tauto.
simpl in |- *.
intros.
elim (eq_dart_dec (top m one x) z).
intro.
rewrite <- a in |- *.
rewrite cA_top in |- *.
tauto.
tauto.
tauto.
elim (eq_dart_dec (cA_1 (B m one x) one (bottom m one x)) z).
intros.
generalize a.
clear a.
rewrite cA_B in |- *.
rewrite cA_1_B in |- *.
elim (eq_dart_dec (A m one x) (bottom m one x)).
elim (eq_dart_dec x (top m one x)).
intros.
symmetry in a0.
absurd (bottom m one x = A m one x).
apply succ_bottom.
tauto.
tauto.
tauto.
elim (eq_dart_dec (top m one x) (top m one x)).
intros.
tauto.
intros.
rewrite a0 in |- *.
tauto.
elim (eq_dart_dec (bottom m one x) (bottom m one x)).
elim (eq_dart_dec x (top m one x)).
intros.
rewrite cA_eq in |- *.
elim (succ_dec m one z).
rewrite <- a1 in b.
symmetry in a.
tauto.
rewrite a1 in |- *.
tauto.
tauto.
elim (eq_dart_dec (top m one x) (top m one x)).
rewrite cA_eq in |- *.
intros.
elim (succ_dec m one z).
rewrite a1 in |- *.
tauto.
rewrite <- a1 in |- *.
tauto.
tauto.
tauto.
tauto.
tauto.
tauto.
tauto.
tauto.
rewrite cA_B in |- *.
rewrite cA_1_B in |- *.
elim (eq_dart_dec (A m one x) (bottom m one x)).
intro.
symmetry in a.
absurd (bottom m one x = A m one x).
apply succ_bottom.
tauto.
tauto.
tauto.
elim (eq_dart_dec (bottom m one x) (bottom m one x)).
elim (eq_dart_dec x z).
tauto.
elim (eq_dart_dec (top m one x) z).
rewrite cA_eq in |- *.
intros.
rewrite a in b2.
tauto.
tauto.
tauto.
tauto.
tauto.
tauto.
tauto.
Admitted.

Lemma cA_L_B_top_bot_ter:forall(m:fmap)(k:dim)(x z:dart), inv_hmap m -> succ m k x -> let k1 := dim_opp k in cA (L (B m k x) k (top m k x) (bottom m k x)) k1 z = cA m k1 z.
Proof.
intros.
unfold k1 in |- *.
induction k.
simpl in |- *.
rewrite cA_B_ter in |- *.
tauto.
tauto.
intro.
inversion H1.
simpl in |- *.
rewrite cA_B_ter in |- *.
tauto.
tauto.
intro.
Admitted.

Lemma A_L_B_top_bot:forall(m:fmap)(k:dim)(x z:dart), inv_hmap m -> succ m k x -> A (L (B m k x) k (top m k x) (bottom m k x)) k z = if eq_dart_dec x z then nil else if eq_dart_dec (top m k x) z then (bottom m k x) else A m k z.
Proof.
intros.
simpl in |- *.
elim (eq_dim_dec k k).
elim (eq_dart_dec (top m k x) z).
intros.
elim (eq_dart_dec x z).
intro.
rewrite <- a1 in a.
rewrite <- a in H0.
absurd (succ m k (top m k x)).
apply not_succ_top.
tauto.
tauto.
tauto.
intros.
elim (eq_dart_dec x z).
intro.
rewrite <- a0 in |- *.
rewrite A_B in |- *.
tauto.
tauto.
intro.
rewrite A_B_bis in |- *.
tauto.
intro.
symmetry in H1.
tauto.
Admitted.

Lemma A_L_B_top_bot_ter:forall(m:fmap)(k:dim)(x z:dart), inv_hmap m -> succ m k x -> let k1:=dim_opp k in A (L (B m k x) k (top m k x) (bottom m k x)) k1 z = A m k1 z.
Proof.
intros.
induction k.
unfold k1 in |- *.
simpl in |- *.
apply A_B_ter.
intro.
inversion H1.
unfold k1 in |- *.
simpl in |- *.
rewrite A_B_ter in |- *.
tauto.
intro.
Admitted.

Lemma cA_1_L_B_top_bot:forall(m:fmap)(k:dim)(x z:dart), inv_hmap m -> succ m k x -> cA_1 (L (B m k x) k (top m k x) (bottom m k x)) k z = cA_1 m k z.
Proof.
induction k.
simpl in |- *.
intros.
assert (exd m x).
apply succ_exd with zero.
tauto.
tauto.
rename H1 into Exx.
elim (eq_dart_dec (bottom m zero x) z).
intro.
rewrite <- a in |- *.
rewrite cA_1_bottom in |- *.
tauto.
tauto.
tauto.
elim (eq_dart_dec (cA (B m zero x) zero (top m zero x)) z).
intros.
generalize a.
clear a.
rewrite cA_B in |- *.
rewrite cA_1_B in |- *.
elim (eq_dart_dec x (top m zero x)).
tauto.
elim (eq_dart_dec (top m zero x) (top m zero x)).
elim (eq_dart_dec (A m zero x) (bottom m zero x)).
intros.
rewrite <- a in b.
tauto.
elim (eq_dart_dec (bottom m zero x) (bottom m zero x)).
intros.
generalize (cA_eq m zero x H).
elim (succ_dec m zero x).
intros.
rewrite <- a1 in |- *.
rewrite <- H1 in |- *.
rewrite cA_1_cA in |- *.
tauto.
tauto.
tauto.
tauto.
tauto.
tauto.
tauto.
tauto.
tauto.
tauto.
intros.
rewrite cA_1_B in |- *.
elim (eq_dart_dec (A m zero x) z).
intro.
generalize b.
rewrite cA_B in |- *.
elim (eq_dart_dec x (top m zero x)).
intros.
rewrite a0 in H0.
absurd (succ m zero (top m zero x)).
apply not_succ_top.
tauto.
tauto.
elim (eq_dart_dec (top m zero x) (top m zero x)).
tauto.
tauto.
tauto.
tauto.
elim (eq_dart_dec (bottom m zero x) z).
tauto.
tauto.
tauto.
tauto.
intros.
assert (exd m x).
apply succ_exd with one.
tauto.
tauto.
simpl in |- *.
elim (eq_dart_dec (bottom m one x) z).
intros.
rewrite <- a in |- *.
rewrite cA_1_bottom in |- *.
tauto.
tauto.
tauto.
elim (eq_dart_dec (cA (B m one x) one (top m one x)) z).
intros.
generalize a.
rewrite cA_B in |- *.
elim (eq_dart_dec x (top m one x)).
intro.
rewrite a0 in H0.
absurd (succ m one (top m one x)).
apply not_succ_top.
tauto.
tauto.
elim (eq_dart_dec (top m one x) (top m one x)).
intros.
rewrite cA_1_B in |- *.
elim (eq_dart_dec (A m one x) (bottom m one x)).
intro.
rewrite a2 in a1.
tauto.
elim (eq_dart_dec (bottom m one x) (bottom m one x)).
intros.
generalize (cA_eq m one x H).
elim (succ_dec m one x).
intros.
rewrite <- a1 in |- *.
rewrite <- H2 in |- *.
rewrite cA_1_cA in |- *.
tauto.
tauto.
tauto.
tauto.
tauto.
tauto.
tauto.
tauto.
tauto.
tauto.
rewrite cA_B in |- *.
rewrite cA_1_B in |- *.
elim (eq_dart_dec x (top m one x)).
intro.
rewrite a in H0.
absurd (succ m one (top m one x)).
apply not_succ_top.
tauto.
tauto.
elim (eq_dart_dec (top m one x) (top m one x)).
elim (eq_dart_dec (A m one x) z).
tauto.
elim (eq_dart_dec (bottom m one x) z).
tauto.
tauto.
tauto.
tauto.
tauto.
tauto.
Admitted.

Lemma cA_1_L_B_top_bot_ter:forall(m:fmap)(k:dim)(x z:dart), inv_hmap m -> succ m k x -> let k1 := dim_opp k in cA_1 (L (B m k x) k (top m k x) (bottom m k x)) k1 z = cA_1 m k1 z.
Proof.
intros.
unfold k1 in |- *.
induction k.
simpl in |- *.
rewrite cA_1_B_ter in |- *.
tauto.
tauto.
intro.
inversion H1.
simpl in |- *.
rewrite cA_1_B_ter in |- *.
tauto.
tauto.
intro.
Admitted.

Lemma A_1_L_B_top_bot:forall(m:fmap)(k:dim)(x z:dart), inv_hmap m -> succ m k x -> A_1 (L (B m k x) k (top m k x) (bottom m k x)) k z = if eq_dart_dec (A m k x) z then nil else if eq_dart_dec (bottom m k x) z then (top m k x) else A_1 m k z.
Proof.
intros.
simpl in |- *.
elim (eq_dim_dec k k).
elim (eq_dart_dec (bottom m k x) z).
elim (eq_dart_dec (A m k x) z).
intros.
rewrite <- a in a0.
absurd (bottom m k x = A m k x).
apply succ_bottom.
tauto.
tauto.
tauto.
tauto.
elim (eq_dart_dec (A m k x) z).
intros.
rewrite <- a in |- *.
apply A_1_B.
tauto.
intros.
rewrite A_1_B_bis in |- *.
tauto.
tauto.
intro.
symmetry in H1.
tauto.
Admitted.

Lemma A_1_L_B_top_bot_ter:forall(m:fmap)(k:dim)(x z:dart), inv_hmap m -> succ m k x -> let k1:=dim_opp k in A_1 (L (B m k x) k (top m k x) (bottom m k x)) k1 z = A_1 m k1 z.
Proof.
intros.
induction k.
unfold k1 in |- *.
simpl in |- *.
apply A_1_B_ter.
intro.
inversion H1.
unfold k1 in |- *.
simpl in |- *.
rewrite A_1_B_ter in |- *.
tauto.
intro.
Admitted.

Lemma inv_hmap_L_B_top_bot:forall(m:fmap)(k:dim)(x:dart), inv_hmap m -> succ m k x -> inv_hmap (L (B m k x) k (top m k x) (bottom m k x)).
Proof.
intros.
simpl in |- *.
split.
apply inv_hmap_B.
tauto.
assert (exd m x).
apply succ_exd with k.
tauto.
tauto.
unfold prec_L in |- *.
split.
generalize (exd_B m k x (top m k x)).
generalize (exd_top m k x).
generalize (succ_exd m k x).
tauto.
split.
generalize (exd_B m k x (bottom m k x)).
generalize (exd_bottom m k x).
generalize (succ_exd m k x).
tauto.
split.
unfold succ in |- *.
rewrite A_B_bis in |- *.
fold (succ m k (top m k x)) in |- *.
apply not_succ_top.
tauto.
intro.
rewrite <- H2 in H0.
generalize H0.
apply not_succ_top.
tauto.
split.
unfold pred in |- *.
rewrite A_1_B_bis in |- *.
fold (pred m k (bottom m k x)) in |- *.
apply not_pred_bottom.
tauto.
tauto.
apply succ_bottom.
tauto.
tauto.
rewrite cA_B in |- *.
elim (eq_dart_dec x (top m k x)).
intro.
rewrite a in H0.
absurd (succ m k (top m k x)).
apply not_succ_top.
tauto.
tauto.
elim (eq_dart_dec (top m k x) (top m k x)).
intros.
intro.
symmetry in H2.
generalize H2.
apply succ_bottom.
tauto.
tauto.
tauto.
tauto.
Admitted.

Lemma exd_L_B_top_bot: forall(m:fmap)(k:dim)(x z:dart), exd m z <-> exd (L (B m k x) k (top m k x) (bottom m k x)) z.
Proof.
intros.
simpl in |- *.
generalize (exd_B m k x z).
Admitted.

Lemma planar_L_B_top_bot_0:forall(m:fmap)(x:dart), inv_hmap m -> succ m zero x -> planar m -> planar (L (B m zero x) zero (top m zero x) (bottom m zero x)).
Proof.
intros.
generalize (inv_hmap_L_B_top_bot m zero x H H0).
intro.
generalize (planarity_criterion_0 (B m zero x) (top m zero x) (bottom m zero x)).
intros.
simpl in H2.
assert (planar (B m zero x)).
apply planar_B0.
tauto.
tauto.
tauto.
assert (planar (L (B m zero x) zero (top m zero x) (bottom m zero x)) <-> ~ eqc (B m zero x) (top m zero x) (bottom m zero x) \/ expf (B m zero x) (cA_1 (B m zero x) one (top m zero x)) (bottom m zero x)).
tauto.
clear H3.
elim (eqc_dec (B m zero x) (top m zero x) (bottom m zero x)).
intro.
assert (expf (B m zero x) (cA_1 (B m zero x) one (top m zero x)) (bottom m zero x)).
rewrite cA_1_B_ter in |- *.
set (xb0 := bottom m zero x) in |- *.
set (xh0 := top m zero x) in |- *.
set (xh0_1 := cA_1 m one xh0) in |- *.
generalize (expf_B0_CNS m x xh0_1 xb0).
simpl in |- *.
set (x_1 := cA_1 m one x) in |- *.
set (x0 := cA m zero x) in |- *.
fold xb0 in |- *.
fold xh0 in |- *.
fold xh0_1 in |- *.
assert (cA m zero x = A m zero x).
rewrite cA_eq in |- *.
elim (succ_dec m zero x).
tauto.
tauto.
tauto.
assert (exd m x).
apply succ_exd with zero.
tauto.
tauto.
generalize (disconnect_planar_criterion_B0 m x H H1 H0).
simpl in |- *.
rewrite <- H3 in |- *.
fold x0 in |- *.
fold xb0 in |- *.
intro.
assert (eqc (B m zero x) x xb0).
unfold xb0 in |- *.
apply eqc_B_bottom.
tauto.
tauto.
assert (eqc (B m zero x) x0 xh0).
unfold x0 in |- *; unfold xh0 in |- *.
rewrite H3 in |- *.
apply eqc_B_top.
tauto.
tauto.
fold xh0 in a.
fold xb0 in a.
assert (eqc (B m zero x) x0 xb0).
apply eqc_trans with xh0.
tauto.
tauto.
assert (eqc (B m zero x) x x0).
apply eqc_trans with xb0.
tauto.
apply eqc_symm.
tauto.
assert (~ expf m x0 xb0).
generalize (expf_dec m x0 xb0).
tauto.
elim (expf_dec m x0 xb0).
tauto.
assert (expf m xh0_1 xb0).
assert (xh0 = cA_1 m zero xb0).
unfold xb0 in |- *.
unfold xh0 in |- *.
rewrite cA_1_bottom in |- *.
tauto.
tauto.
tauto.
unfold xh0_1 in |- *.
rewrite H13 in |- *.
fold (cF m xb0) in |- *.
unfold expf in |- *.
split.
tauto.
apply MF.expo_symm.
tauto.
unfold MF.expo in |- *.
split.
generalize (exd_cF m xb0).
assert (exd m xb0).
unfold xb0 in |- *.
apply exd_bottom.
tauto.
tauto.
tauto.
split with 1%nat.
simpl in |- *.
tauto.
tauto.
tauto.
intro.
inversion H3.
tauto.
Admitted.

Lemma between_bottom_x_top: forall(m:fmap)(x:dart), inv_hmap m -> succ m zero x -> betweene m (bottom m zero x) x (top m zero x).
Proof.
unfold betweene in |- *.
unfold MA0.between in |- *.
intros.
assert (exd m x).
apply succ_exd with zero.
tauto.
tauto.
generalize (expe_bottom_z m x H H3).
intro.
assert (MA0.expo1 m (bottom m zero x) x).
generalize (MA0.expo_expo1 m (bottom m zero x) x).
tauto.
unfold MA0.expo1 in H5.
elim H5.
clear H5.
intros.
elim H6.
clear H6.
intros i Hi.
split with i.
generalize (MA0.upb_pos m (bottom m zero x) H5).
intro.
set (p := MA0.Iter_upb m (bottom m zero x)) in |- *.
fold p in H6.
fold p in Hi.
split with (p - 1)%nat.
split.
tauto.
split.
rewrite <- cA_1_bottom in |- *.
assert (cA_1 m zero (bottom m zero x) = MA0.f_1 m (bottom m zero x)).
tauto.
rewrite H7 in |- *.
rewrite <- MA0.Iter_f_f_1 in |- *.
simpl in |- *.
unfold p in |- *.
rewrite MA0.Iter_upb_period in |- *.
tauto.
tauto.
tauto.
tauto.
tauto.
omega.
tauto.
tauto.
Admitted.

Lemma top_L_B_top_bot:forall(m:fmap)(x z:dart)(H:inv_hmap m), succ m zero x -> exd m z -> x <> z -> let m0:= L (B m zero x) zero (top m zero x) (bottom m zero x) in top m0 zero z = if MA0.expo_dec m x z H then x else top m zero z.
Proof.
intros.
generalize (bottom_L_B_top_bot m x z H H0 H1 H2).
intros.
rewrite <- (cA_1_bottom m0 zero z) in |- *.
unfold m0 in H3.
fold m0 in H3.
rewrite H3 in |- *.
elim (MA0.expo_dec m x z H).
assert (cA m zero x = A m zero x).
rewrite cA_eq in |- *.
elim (succ_dec m zero x).
tauto.
tauto.
tauto.
rewrite <- H4 in |- *.
assert (cA m0 zero x = cA m zero x).
unfold m0 in |- *.
rewrite cA_L_B_top_bot in |- *.
tauto.
tauto.
tauto.
rewrite <- H5 in |- *.
rewrite cA_1_cA in |- *.
tauto.
unfold m0 in |- *.
apply inv_hmap_L_B_top_bot.
tauto.
tauto.
unfold m0 in |- *.
generalize (exd_L_B_top_bot m zero x x).
assert (exd m x).
apply succ_exd with zero.
tauto.
tauto.
tauto.
generalize H3.
elim (MA0.expo_dec m x z H).
tauto.
intros.
unfold m0 in |- *.
rewrite cA_1_L_B_top_bot in |- *.
apply cA_1_bottom.
tauto.
tauto.
tauto.
tauto.
unfold m0 in |- *; apply inv_hmap_L_B_top_bot.
tauto.
tauto.
unfold m0 in |- *.
generalize (exd_L_B_top_bot m zero x z).
Admitted.

Lemma cF_L_B_top_bot:forall(m:fmap)(k:dim)(x z:dart), inv_hmap m -> succ m k x -> cF (L (B m k x) k (top m k x) (bottom m k x)) z = cF m z.
Proof.
intros.
unfold cF in |- *.
induction k.
rewrite cA_1_L_B_top_bot in |- *.
rewrite (cA_1_L_B_top_bot_ter m zero x) in |- *.
simpl in |- *.
tauto.
tauto.
tauto.
tauto.
tauto.
rewrite (cA_1_L_B_top_bot_ter m one x) in |- *.
rewrite cA_1_L_B_top_bot in |- *.
simpl in |- *.
tauto.
tauto.
tauto.
tauto.
Admitted.

Lemma cF_1_L_B_top_bot:forall(m:fmap)(k:dim)(x z:dart), inv_hmap m -> succ m k x -> cF_1 (L (B m k x) k (top m k x) (bottom m k x)) z = cF_1 m z.
Proof.
intros.
unfold cF_1 in |- *.
induction k.
rewrite (cA_L_B_top_bot_ter m zero x) in |- *.
rewrite cA_L_B_top_bot in |- *.
simpl in |- *.
tauto.
tauto.
tauto.
tauto.
tauto.
rewrite (cA_L_B_top_bot m one x) in |- *.
rewrite (cA_L_B_top_bot_ter m one x) in |- *.
simpl in |- *.
tauto.
tauto.
tauto.
tauto.
Admitted.

Lemma Iter_f_L_B: forall(m:fmap)(k:dim)(x z:dart)(i:nat), inv_hmap m -> succ m k x -> let m0:= L (B m k x) k (top m k x) (bottom m k x) in Iter (MF.f m0) i z = Iter (MF.f m) i z.
Proof.
intros.
induction i.
simpl in |- *.
tauto.
simpl in |- *.
rewrite IHi in |- *.
assert (MF.f = cF).
tauto.
rewrite H1 in |- *.
unfold m0 in |- *.
apply cF_L_B_top_bot.
tauto.
Admitted.

Lemma expf_L_B_top_bot:forall(m:fmap)(k:dim)(x z t:dart), inv_hmap m -> succ m k x -> (expf (L (B m k x) k (top m k x) (bottom m k x)) z t <-> expf m z t).
Proof.
intros.
unfold expf in |- *.
generalize (inv_hmap_L_B_top_bot m k x).
intro.
assert (MF.expo (L (B m k x) k (top m k x) (bottom m k x)) z t <-> MF.expo m z t).
unfold MF.expo in |- *.
assert (exd m x).
apply succ_exd with k.
tauto.
tauto.
generalize (exd_L_B_top_bot m k x z).
intro.
split.
intros.
decompose [and] H4.
clear H4.
elim H6.
clear H6.
intros i Hi.
split.
tauto.
split with i.
rewrite <- Hi in |- *.
symmetry in |- *.
apply Iter_f_L_B.
tauto.
tauto.
intro.
decompose [and] H4.
clear H4.
elim H6.
clear H6.
intros i Hi.
split.
tauto.
split with i.
rewrite <- Hi in |- *.
apply Iter_f_L_B.
tauto.
tauto.
Admitted.

Lemma nc_L_B_top_bot :forall(m:fmap)(k:dim)(x:dart), inv_hmap m -> succ m k x -> let m0:= L (B m k x) k (top m k x) (bottom m k x) in nc m0 = nc m.
Proof.
simpl in |- *.
intros.
rewrite nc_B in |- *.
assert (exd m x).
apply succ_exd with k.
tauto.
tauto.
generalize (eqc_B_top m k x H H0).
generalize (eqc_B_bottom m k x H H1).
intros.
elim (eqc_dec (B m k x) x (A m k x)).
elim (eqc_dec (B m k x) (top m k x) (bottom m k x)).
intros.
omega.
intros.
elim b.
apply eqc_trans with (A m k x).
apply eqc_symm.
tauto.
apply eqc_trans with x.
apply eqc_symm.
tauto.
tauto.
elim (eqc_dec (B m k x) (top m k x) (bottom m k x)).
intros.
elim b.
apply eqc_trans with (bottom m k x).
tauto.
apply eqc_trans with (top m k x).
apply eqc_symm.
tauto.
apply eqc_symm.
tauto.
intros.
omega.
tauto.
Admitted.

Lemma eqc_L_B_top_bot:forall (m:fmap)(k:dim)(x z t:dart), inv_hmap m -> succ m k x -> let m0:= L (B m k x) k (top m k x) (bottom m k x) in eqc m0 z t <-> eqc m z t.
Proof.
simpl in |- *.
intros.
generalize (eqc_B m k x z t H H0).
simpl in |- *.
intro.
generalize (eqc_B_top m k x H H0).
intro.
assert (exd m x).
apply succ_exd with k.
tauto.
tauto.
generalize (eqc_B_bottom m k x H H3).
intro.
elim H1.
clear H1.
intros.
split.
clear H1.
intro.
elim H1.
tauto.
clear H1.
intro.
elim H1.
clear H1.
intro.
assert (eqc (B m k x) z (A m k x)).
apply eqc_trans with (top m k x).
tauto.
apply eqc_symm.
tauto.
assert (eqc (B m k x) x t).
apply eqc_trans with (bottom m k x).
tauto.
tauto.
tauto.
clear H1.
intro.
assert (eqc (B m k x) z x).
apply eqc_trans with (bottom m k x).
tauto.
apply eqc_symm.
tauto; tauto.
assert (eqc (B m k x) (A m k x) t).
apply eqc_trans with (top m k x).
tauto.
tauto.
tauto.
clear H5.
intro.
elim H1.
clear H1.
intro.
tauto.
clear H1.
intro.
elim H1.
clear H1.
intro.
right.
right.
split.
apply eqc_trans with x.
tauto.
tauto.
apply eqc_trans with (A m k x).
apply eqc_symm.
tauto.
tauto.
clear H1.
intro.
right.
left.
split.
apply eqc_trans with (A m k x).
tauto.
tauto.
apply eqc_trans with x.
apply eqc_symm.
tauto.
tauto.
Admitted.

Lemma MA0_f_cA0:forall(m:fmap)(z:dart), MA0.f m z = cA m zero z.
Proof.
Admitted.

Lemma Iter_cA0_L_B: forall(m:fmap)(k:dim)(x z:dart)(i:nat), inv_hmap m -> succ m k x -> let m0:= L (B m k x) k (top m k x) (bottom m k x) in Iter (MA0.f m0) i z = Iter (MA0.f m) i z.
Proof.
intros.
induction i.
simpl in |- *.
tauto.
simpl in |- *.
rewrite IHi in |- *.
rewrite MA0_f_cA0 in |- *.
rewrite MA0_f_cA0 in |- *.
unfold m0 in |- *.
induction k.
rewrite cA_L_B_top_bot in |- *.
tauto.
tauto.
tauto.
assert (zero = dim_opp one).
simpl in |- *.
tauto.
rewrite H1 in |- *.
apply cA_L_B_top_bot_ter.
tauto.
Admitted.

Lemma expe_L_B_top_bot:forall (m:fmap)(x z t:dart), inv_hmap m -> succ m zero x -> let m0:= L (B m zero x) zero (top m zero x) (bottom m zero x) in expe m0 z t <-> expe m z t.
Proof.
intros.
unfold expe in |- *.
split.
intro.
assert (inv_hmap m0).
unfold m0 in |- *.
apply inv_hmap_L_B_top_bot.
tauto.
tauto.
assert (exd m0 t).
apply MA0.expo_exd with z.
tauto.
tauto.
assert (exd m t).
generalize (exd_L_B_top_bot m zero x t).
unfold m0 in H2.
tauto.
assert (exd m0 z).
unfold MA0.expo in H1.
tauto.
generalize H1.
clear H1.
unfold MA0.expo in |- *.
assert (exd m z).
generalize (exd_L_B_top_bot m zero x z).
unfold m0 in H2.
tauto.
intro.
split.
tauto.
elim H6.
clear H6.
intros.
elim H7.
clear H7.
intros i Hi.
split with i.
generalize (Iter_cA0_L_B m zero x z i H H0).
simpl in |- *.
fold m0 in |- *.
intro.
rewrite <- H7 in |- *.
tauto.
intro.
assert (exd m z).
unfold MA0.expo in H1.
tauto.
assert (exd m0 z).
unfold m0 in |- *.
generalize (exd_L_B_top_bot m zero x z).
tauto.
unfold MA0.expo in H1.
elim H1.
clear H1.
intro.
intro.
elim H4.
intros i Hi.
clear H4.
unfold MA0.expo in |- *.
split.
tauto.
split with i.
unfold m0 in |- *.
rewrite <- Hi in |- *.
apply Iter_cA0_L_B.
tauto.
Admitted.

Lemma exd_Br1:forall(m:fmap)(x x' z:dart), exd m z <-> exd (Br1 m x x') z.
Proof.
unfold Br1 in |- *.
intros.
elim (succ_dec m zero x).
elim (succ_dec m zero x').
intros.
generalize (exd_B (L (B m zero x) zero (top m zero x) (bottom m zero x)) zero x' z).
simpl in |- *.
generalize (exd_B m zero x z).
tauto.
generalize (exd_B m zero x z).
tauto.
generalize (exd_B m zero x' z).
Admitted.

Lemma inv_hmap_Br1:forall(m:fmap)(x x':dart), inv_hmap m -> inv_hmap (Br1 m x x').
Proof.
unfold Br1 in |- *.
intros.
elim (succ_dec m zero x).
intro.
elim (succ_dec m zero x').
intros.
apply inv_hmap_B.
apply inv_hmap_L_B_top_bot.
tauto.
tauto.
intro.
apply inv_hmap_B.
tauto.
intro.
elim (succ_dec m zero x').
intro.
apply inv_hmap_B.
tauto.
intro.
rewrite not_succ_B in |- *.
tauto.
tauto.
Admitted.

Lemma planar_Br1:forall(m:fmap)(x x':dart), inv_hmap m -> planar m -> x <> x' -> planar (Br1 m x x').
Proof.
intros.
unfold Br1 in |- *.
elim (succ_dec m zero x).
elim (succ_dec m zero x').
intros.
apply planar_B0.
apply inv_hmap_L_B_top_bot.
tauto.
tauto.
unfold succ in |- *.
simpl in |- *.
elim (eq_dart_dec (top m zero x) x').
intro.
rewrite <- a1 in a.
absurd (succ m zero (top m zero x)).
apply not_succ_top.
tauto.
tauto.
intro.
rewrite A_B_bis in |- *.
unfold succ in a.
tauto.
intro.
symmetry in H2.
tauto.
apply planar_L_B_top_bot_0.
tauto.
tauto.
tauto.
intros.
apply planar_B0.
tauto.
tauto.
tauto.
intro.
elim (succ_dec m zero x').
intro.
apply planar_B0.
tauto.
tauto.
tauto.
intro.
rewrite not_succ_B in |- *.
tauto.
tauto.
Admitted.

Lemma double_link_comm: forall (m:fmap)(x x':dart), inv_hmap m -> double_link m x x' -> double_link m x' x.
Proof.
unfold double_link in |- *.
intros.
split.
intro.
symmetry in H1.
tauto.
unfold expe in |- *.
unfold expe in H.
apply MA0.expo_symm.
tauto.
Admitted.

Lemma double_link_succ :forall (m:fmap)(x x':dart), inv_hmap m -> double_link m x x' -> (succ m zero x \/ succ m zero x').
Proof.
intros.
unfold double_link in H0.
elim (succ_dec m zero x).
tauto.
elim (succ_dec m zero x').
tauto.
intros.
assert (exd m x).
unfold expe in H0.
unfold MA0.expo in H0.
tauto.
assert (exd m x').
unfold expe in H0.
apply MA0.expo_exd with x.
tauto.
tauto.
assert (top m zero x = x).
apply nosucc_top.
tauto.
tauto.
tauto.
assert (top m zero x' = x').
apply nosucc_top.
tauto.
tauto.
tauto.
elim H0.
intros.
elim H5.
rewrite <- H3 in |- *.
rewrite <- H4 in |- *.
apply expe_top.
tauto.
Admitted.

Lemma double_link_exd:forall(m:fmap)(x x':dart), inv_hmap m -> double_link m x x' -> exd m x /\ exd m x'.
Proof.
unfold double_link in |- *.
unfold expe in |- *.
intros.
generalize (MA0.expo_exd m x x').
intro.
unfold double_link in |- *.
unfold expe in |- *.
intros.
generalize (MA0.expo_exd m x x').
intro.
assert (exd m x).
unfold MA0.expo in H0.
tauto.
Admitted.

Lemma cA0_Br1:forall(m:fmap)(x x' z:dart), inv_hmap m -> double_link m x x' -> cA (Br1 m x x') zero z = if eq_dart_dec x z then cA m zero x' else if eq_dart_dec x' z then cA m zero x else cA m zero z.
Proof.
intros.
generalize (double_link_exd m x x' H H0).
intro Exx'.
unfold double_link in H0.
unfold expe in H0.
unfold Br1 in |- *.
set (m0 := L (B m zero x) zero (top m zero x) (bottom m zero x)) in |- *.
elim (succ_dec m zero x).
elim (succ_dec m zero x').
intros.
unfold m0 in |- *.
rewrite cA_B in |- *.
elim (eq_dart_dec x' z).
intro.
rewrite (bottom_L_B_top_bot m x x' H a0) in |- *.
elim (MA0.expo_dec m x x' H).
intro.
elim (eq_dart_dec x z).
intro.
rewrite <- a1 in a3.
rewrite cA_eq in |- *.
elim (succ_dec m zero x').
rewrite a3 in |- *.
tauto.
tauto.
tauto.
rewrite cA_eq in |- *.
elim (succ_dec m zero x).
tauto.
tauto.
tauto.
tauto.
tauto.
tauto.
elim (eq_dart_dec (top (L (B m zero x) zero (top m zero x) (bottom m zero x)) zero x') z).
intros.
rewrite (top_L_B_top_bot m x x' H) in a1.
generalize a1.
clear a1.
elim (MA0.expo_dec m x x').
intros.
rewrite A_L_B_top_bot in |- *.
elim (eq_dart_dec x x').
tauto.
elim (eq_dart_dec (top m zero x) x').
intros.
rewrite <- a3 in a.
absurd (succ m zero (top m zero x)).
apply not_succ_top.
tauto.
tauto.
elim (eq_dart_dec x z).
rewrite cA_eq in |- *.
elim (succ_dec m zero x').
tauto.
tauto.
tauto.
tauto.
tauto.
tauto.
tauto.
tauto.
tauto.
tauto.
rewrite (top_L_B_top_bot m x x' H) in |- *.
elim (MA0.expo_dec m x x' H).
intros.
rewrite cA_L_B_top_bot in |- *.
elim (eq_dart_dec x z).
tauto.
tauto.
tauto.
tauto.
tauto.
tauto.
tauto.
tauto.
apply inv_hmap_L_B_top_bot.
tauto.
tauto.
unfold succ in |- *.
simpl in |- *.
elim (eq_dart_dec (top m zero x) x').
intro.
rewrite <- a1 in a.
absurd (succ m zero (top m zero x)).
apply not_succ_top.
tauto.
tauto.
rewrite A_B_bis in |- *.
unfold succ in a.
tauto.
intro.
symmetry in H1.
tauto.
intros.
rewrite cA_B in |- *.
elim (eq_dart_dec x z).
intros.
rewrite cA_eq in |- *.
elim (succ_dec m zero x').
tauto.
intro.
apply expe_bottom.
tauto.
tauto.
tauto.
elim (eq_dart_dec (top m zero x) z).
elim (eq_dart_dec x' z).
rewrite cA_eq in |- *.
elim (succ_dec m zero x).
tauto.
tauto.
tauto.
intros.
rewrite cA_eq in |- *.
elim (succ_dec m zero z).
intro.
rewrite <- a0 in a1.
absurd (succ m zero (top m zero x)).
apply not_succ_top.
tauto.
tauto.
intros.
assert (top m zero x = top m zero x').
apply expe_top.
tauto.
tauto.
rewrite a0 in H1.
generalize (nosucc_top m zero x' H).
intro.
rewrite H2 in H1.
symmetry in H1.
tauto.
tauto.
tauto.
tauto.
elim (eq_dart_dec x' z).
intros.
rewrite <- a0 in b0.
generalize (expe_top m x x').
intros.
rewrite H1 in b0.
elim b0.
apply nosucc_top.
tauto.
tauto.
tauto.
tauto.
tauto.
tauto.
tauto.
tauto.
intro.
elim (eq_dart_dec x z).
rewrite cA_B in |- *.
elim (eq_dart_dec x' z).
intros.
rewrite <- a in a0.
tauto.
elim (eq_dart_dec (top m zero x') z).
intros.
rewrite cA_eq in |- *.
elim (succ_dec m zero x').
tauto.
intros.
assert (top m zero x = top m zero x').
apply (expe_top m x x').
tauto.
tauto.
generalize (nosucc_top m zero x').
intro.
rewrite H2 in a.
tauto.
tauto.
tauto.
tauto.
tauto.
intros.
assert (top m zero x = top m zero x').
apply expe_top.
tauto.
tauto.
rewrite <- H1 in b0.
generalize (nosucc_top m zero x).
intro.
rewrite H2 in b0.
tauto.
tauto.
tauto.
tauto.
tauto.
elim (succ_dec m zero x').
tauto.
intro.
assert (top m zero x = top m zero x').
apply expe_top.
tauto.
tauto.
generalize (nosucc_top m zero x).
generalize (nosucc_top m zero x').
intros.
rewrite H2 in H1.
rewrite H3 in H1.
tauto.
tauto.
tauto.
tauto.
tauto.
tauto.
tauto.
intro.
rewrite cA_B in |- *.
elim (eq_dart_dec x' z).
intros.
rewrite cA_eq in |- *.
elim (succ_dec m zero x).
tauto.
intro.
apply expe_bottom.
tauto.
apply MA0.expo_symm.
tauto.
tauto.
tauto.
elim (eq_dart_dec (top m zero x') z).
intros.
assert (top m zero x = top m zero x').
apply expe_top.
tauto.
tauto.
rewrite <- H1 in a.
generalize (nosucc_top m zero x).
intro.
rewrite H2 in a.
tauto.
tauto.
tauto.
tauto.
tauto.
tauto.
elim (succ_dec m zero x').
tauto.
intro.
assert (top m zero x = top m zero x').
apply expe_top.
tauto.
tauto.
generalize (nosucc_top m zero x).
generalize (nosucc_top m zero x').
intros.
rewrite H2 in H1.
rewrite H3 in H1.
tauto.
tauto.
tauto.
tauto.
tauto.
tauto.
Admitted.

Lemma cA0_1_Br1:forall(m:fmap)(x x' z:dart), inv_hmap m -> double_link m x x' -> cA_1 (Br1 m x x') zero z = if eq_dart_dec (cA m zero x) z then x' else if eq_dart_dec (cA m zero x') z then x else cA_1 m zero z.
Proof.
intros.
generalize (double_link_exd m x x' H H0).
intro Exx'.
elim (exd_dec m z).
intro.
set (t := cA_1 (Br1 m x x') zero z) in |- *.
assert (z = cA (Br1 m x x') zero t).
unfold t in |- *.
rewrite cA_cA_1 in |- *.
tauto.
apply inv_hmap_Br1.
tauto.
generalize (exd_Br1 m x x' z).
tauto.
generalize H1.
rewrite cA0_Br1 in |- *.
elim (eq_dart_dec x t).
intros.
elim (eq_dart_dec (cA m zero x) z).
intro.
unfold double_link in H0.
assert (x = cA_1 m zero z).
rewrite <- a1 in |- *.
rewrite cA_1_cA in |- *.
tauto.
tauto.
tauto.
rewrite H2 in H3.
rewrite cA_1_cA in H3.
tauto.
tauto.
tauto.
unfold double_link in |- *.
elim (eq_dart_dec (cA m zero x') z).
intros.
symmetry in |- *.
tauto.
symmetry in H2.
tauto.
elim (eq_dart_dec x' t).
intros.
elim (eq_dart_dec (cA m zero x) z).
symmetry in a0.
tauto.
symmetry in H2.
tauto.
elim (eq_dart_dec (cA m zero x) z).
intros.
assert (x = cA_1 m zero z).
rewrite <- a0 in |- *.
rewrite cA_1_cA in |- *.
tauto.
tauto.
unfold double_link in H0.
tauto.
rewrite H2 in H3.
rewrite cA_1_cA in H3.
tauto.
tauto.
apply cA_exd with zero.
tauto.
rewrite <- H2 in |- *.
apply exd_not_nil with m.
tauto.
tauto.
intros.
symmetry in H2.
elim (eq_dart_dec (cA m zero x') z).
intro.
assert (t = cA_1 m zero z).
rewrite <- H2 in |- *.
rewrite cA_1_cA in |- *.
tauto.
tauto.
apply cA_exd with zero.
tauto.
rewrite H2 in |- *.
apply exd_not_nil with m.
tauto.
tauto.
rewrite <- a0 in H3.
rewrite cA_1_cA in H3.
symmetry in H3.
tauto.
tauto.
unfold double_link in H0.
tauto.
intro.
rewrite <- H2 in |- *.
rewrite cA_1_cA in |- *.
tauto.
tauto.
apply cA_exd with zero.
tauto.
rewrite H2 in |- *.
apply exd_not_nil with m.
tauto.
tauto.
tauto.
tauto.
intro.
unfold double_link in H0.
assert (cA_1 (Br1 m x x') zero z = nil).
apply not_exd_cA_1.
apply inv_hmap_Br1.
tauto.
generalize (exd_Br1 m x x' z).
generalize (exd_dec m z).
generalize (exd_dec (Br1 m x x') z).
tauto.
elim (eq_dart_dec (cA m zero x) z).
intro.
rewrite <- a in b.
generalize (exd_cA_cA_1 m zero x).
tauto.
elim (eq_dart_dec (cA m zero x') z).
intros.
rewrite <- a in b.
generalize (exd_cA_cA_1 m zero x').
tauto.
intros.
rewrite H1 in |- *.
rewrite not_exd_cA_1 in |- *.
tauto.
tauto.
Admitted.

Lemma cA1_Br1:forall(m:fmap)(x x' z:dart), inv_hmap m -> cA (Br1 m x x') one z = cA m one z.
Proof.
unfold Br1 in |- *.
intros.
elim (succ_dec m zero x).
elim (succ_dec m zero x').
intros.
rewrite cA_B_ter in |- *.
simpl in |- *.
rewrite cA_B_ter in |- *.
tauto.
tauto.
intro.
inversion H0.
apply inv_hmap_L_B_top_bot.
tauto.
tauto.
intro.
inversion H0.
intros.
rewrite cA_B_ter in |- *.
tauto.
tauto.
intro.
inversion H0.
rewrite cA_B_ter in |- *.
tauto.
tauto.
intro.
Admitted.

Lemma cA1_1_Br1:forall(m:fmap)(x x' z:dart), inv_hmap m -> cA_1 (Br1 m x x') one z = cA_1 m one z.
Proof.
unfold Br1 in |- *.
intros.
elim (succ_dec m zero x).
elim (succ_dec m zero x').
intros.
rewrite cA_1_B_ter in |- *.
simpl in |- *.
rewrite cA_1_B_ter in |- *.
tauto.
tauto.
intro.
inversion H0.
apply inv_hmap_L_B_top_bot.
tauto.
tauto.
intro.
inversion H0.
intros.
rewrite cA_1_B_ter in |- *.
tauto.
tauto.
intro.
inversion H0.
rewrite cA_1_B_ter in |- *.
tauto.
tauto.
intro.
Admitted.

Lemma bottom_L_B_top_bot: forall(m:fmap)(x z:dart)(H:inv_hmap m), succ m zero x -> exd m z -> x <> z -> let m0:= L (B m zero x) zero (top m zero x) (bottom m zero x) in bottom m0 zero z = if MA0.expo_dec m x z H then (A m zero x) else bottom m zero z.
Proof.
intros.
unfold m0 in |- *.
simpl in |- *.
assert (exd m x).
apply succ_exd with zero.
tauto.
tauto.
assert (exd m (top m zero x)).
apply exd_top.
tauto.
tauto.
assert (x <> top m zero x).
intro.
rewrite H5 in H0.
absurd (succ m zero (top m zero x)).
apply not_succ_top.
tauto.
tauto.
generalize (between_bottom_B0_bis m x (top m zero x) H H4 H3 H5).
simpl in |- *.
rewrite bottom_top_bis in |- *.
intros.
generalize (between_bottom_B0_bis m x z H H1 H3 H2).
simpl in |- *.
intros.
assert (exd m (bottom m zero x)).
apply exd_bottom.
tauto.
tauto.
generalize (betweene_dec1 m (bottom m zero x) x (top m zero x) H H8 H3).
assert (exd m (bottom m zero z)).
apply exd_bottom.
tauto.
tauto.
generalize (betweene_dec1 m (bottom m zero z) x z H H9 H3).
intro.
intro.
decompose [and] H6.
decompose [and] H7.
clear H6 H7.
generalize (not_expe_bottom_B0 m x z H H1 H3).
simpl in |- *.
unfold expe in |- *.
intro.
elim H10.
clear H10.
intro.
generalize (H14 H7).
intro.
clear H14.
rewrite H10 in |- *.
elim (eq_dart_dec (bottom m zero x) (A m zero x)).
intro.
absurd (bottom m zero x = A m zero x).
apply succ_bottom.
tauto.
tauto.
tauto.
intro.
elim (MA0.expo_dec m x z H).
tauto.
intro.
unfold betweene in H7.
generalize (MA0.between_expo m (bottom m zero z) x z).
intros.
elim b0.
apply MA0.expo_trans with (bottom m zero z).
apply MA0.expo_symm.
tauto.
tauto.
tauto.
intro.
generalize (H15 H7).
clear H15.
intro.
rewrite H15 in |- *.
elim (MA0.expo_dec m x z H).
intro.
elim (eq_dart_dec (bottom m zero x) (bottom m zero z)).
intros.
apply H12.
unfold betweene in |- *.
apply betweene_bottom_x_top.
tauto.
tauto.
intro.
elim b.
apply expe_bottom.
tauto.
tauto.
elim (eq_dart_dec (bottom m zero x) (bottom m zero z)).
intros.
elim b.
clear b.
apply MA0.expo_trans with (bottom m zero x).
apply MA0.expo_symm.
tauto.
apply expe_bottom_z.
tauto.
tauto.
rewrite a in |- *.
apply expe_bottom_z.
tauto.
tauto.
tauto.
tauto.
tauto.
