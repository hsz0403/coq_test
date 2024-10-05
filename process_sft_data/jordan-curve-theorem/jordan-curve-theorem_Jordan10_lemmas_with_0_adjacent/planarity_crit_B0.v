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

Theorem planarity_crit_B0: forall (m:fmap)(x:dart), inv_hmap m -> succ m zero x -> let m0 := B m zero x in let y := A m zero x in (planar m <-> (planar m0 /\ (~eqc m0 x y \/ expf m0 (cA_1 m0 one x) y))).
Proof.
intros.
assert (inv_hmap (B m zero x)).
apply inv_hmap_B.
tauto.
assert (genus (B m zero x) >= 0).
apply genus_corollary.
tauto.
generalize H2.
unfold planar in |- *.
unfold genus in |- *.
unfold ec in |- *.
unfold m0 in |- *.
rewrite nc_B.
rewrite nv_B.
rewrite ne_B.
rewrite ndZ_B.
rewrite nf_B0.
assert (cA m zero x = A m zero x).
rewrite cA_eq.
elim (succ_dec m zero x).
tauto.
tauto.
tauto.
generalize (expf_not_expf_B0 m x H H0).
simpl in |- *.
rewrite H3.
rewrite cA_1_B_ter.
fold y in |- *.
fold m0 in |- *.
set (x_1 := cA_1 m one x) in |- *.
set (x0 := bottom m zero x) in |- *.
intro.
elim (expf_dec m y x0).
elim (eqc_dec m0 x y).
intros.
assert (nv m + 0 + (ne m + 1) + (nf m + 1) - nd m = nv m + ne m + nf m - nd m + 1 * 2).
clear H4 H5.
omega.
rewrite H6.
rewrite H6 in H5.
clear H6.
rewrite Zdiv.Z_div_plus.
rewrite Zdiv.Z_div_plus in H5.
set (z := nv m + ne m + nf m - nd m) in |- *.
fold z in H5.
split.
intro.
absurd (nc m + 0 - (Z.div z 2 + 1) >= 0).
clear a0 H4.
omega.
tauto.
tauto.
clear a0 H4.
omega.
clear a0 H4.
omega.
intros.
assert (nv m + 0 + (ne m + 1) + (nf m + 1) - nd m = nv m + ne m + nf m - nd m + 1 * 2).
clear a H4.
omega.
rewrite H6 in H5.
rewrite H6.
clear H6.
rewrite Zdiv.Z_div_plus in H5.
rewrite Zdiv.Z_div_plus.
set (z := nv m + ne m + nf m - nd m) in |- *.
fold z in H5.
assert (nc m - Z.div z 2 = nc m + 1 - (Z.div z 2 + 1)).
clear a H4.
omega.
rewrite H6.
tauto.
clear a H4.
omega.
clear a H4.
omega.
elim (eqc_dec m0 x y).
intros.
assert (nv m + 0 + (ne m + 1) + (nf m + -1) - nd m = nv m + ne m + nf m - nd m).
clear b H4.
omega.
rewrite H6.
clear H6.
assert (nc m - Z.div (nv m + ne m + nf m - nd m) 2 = nc m + 0 - Z.div (nv m + ne m + nf m - nd m) 2).
clear b H4.
omega.
rewrite H6.
clear H6.
tauto.
intros.
assert (cA_1 m0 one x = cA_1 m one x).
unfold m0 in |- *.
rewrite cA_1_B_ter.
tauto.
tauto.
intro.
inversion H6.
assert (eqc m0 x_1 y).
apply expf_eqc.
unfold m0 in |- *.
tauto.
unfold expf in H4.
unfold expf in b0.
tauto.
elim b.
apply eqc_cA_1_eqc with one.
unfold m0 in |- *; tauto.
rewrite H6.
fold x_1 in |- *.
tauto.
tauto.
intro.
inversion H4.
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
