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

Theorem nc_Br1: forall (m:fmap)(x x':dart), inv_hmap m -> planar m -> double_link m x x' -> let y := cA m zero x in let y' := cA m zero x' in nc (Br1 m x x') = nc m + if expf_dec m y y' then 1 else 0.
Proof.
intros.
unfold Br1 in |- *.
elim (succ_dec m zero x).
elim (succ_dec m zero x').
intros.
set (m0 := L (B m zero x) zero (top m zero x) (bottom m zero x)) in |- *.
assert (inv_hmap m0).
unfold m0 in |- *.
apply inv_hmap_L_B_top_bot.
tauto.
tauto.
assert (succ m0 zero x').
unfold succ in |- *.
unfold m0 in |- *.
rewrite A_L_B_top_bot in |- *.
elim (eq_dart_dec x x').
elim (eq_dart_dec (top m zero x) x').
intros.
rewrite <- a1 in a.
absurd (succ m zero (top m zero x)).
apply not_succ_top.
tauto.
tauto.
unfold double_link in H1.
tauto.
elim (eq_dart_dec (top m zero x) x').
intros.
rewrite <- a1 in a.
absurd (succ m zero (top m zero x)).
apply not_succ_top.
tauto.
tauto.
unfold succ in a.
tauto.
tauto.
tauto.
assert (y = bottom m0 zero x').
unfold m0 in |- *.
unfold double_link in H1.
assert (x <> x').
tauto.
assert (exd m x').
apply MA0.expo_exd with x.
tauto.
unfold expe in H1.
tauto.
rewrite (bottom_L_B_top_bot m x x' H a0 H5 H4) in |- *.
elim (MA0.expo_dec m x x').
unfold y in |- *.
rewrite cA_eq in |- *.
elim (succ_dec m zero x).
tauto.
tauto.
tauto.
tauto.
assert (y' = A m0 zero x').
unfold m0 in |- *.
rewrite A_L_B_top_bot in |- *.
elim (eq_dart_dec x x').
unfold double_link in H1.
tauto.
elim (eq_dart_dec (top m zero x) x').
intro.
rewrite <- a1 in a.
absurd (succ m zero (top m zero x)).
apply not_succ_top.
tauto.
tauto.
intros.
unfold y' in |- *.
rewrite cA_eq in |- *.
elim (succ_dec m zero x').
tauto.
tauto.
tauto.
tauto.
tauto.
generalize (expf_L_B_top_bot m zero x y y' H a0).
fold m0 in |- *.
intro.
assert (nc m0 = nc m).
unfold m0 in |- *.
rewrite nc_L_B_top_bot in |- *.
tauto.
tauto.
tauto.
rewrite nc_B in |- *.
assert (planar m0).
unfold m0 in |- *.
apply planar_L_B_top_bot_0.
tauto.
tauto.
tauto.
generalize (disconnect_planar_criterion_B0 m0 x' H2 H8 H3).
intro.
rewrite <- H5 in H9.
rewrite <- H4 in H9.
assert (expf m0 y' y <-> ~ eqc (B m0 zero x') x' y').
apply H9.
rewrite <- H5 in |- *.
clear H9.
rewrite <- H7 in |- *.
elim (eqc_dec (B m0 zero x') x' y').
elim (expf_dec m y y').
intro.
assert (expf m0 y' y).
apply expf_symm.
tauto.
tauto.
tauto.
elim (expf_dec m y y').
intro.
assert (expf m0 y' y).
apply expf_symm.
tauto.
tauto.
intros.
assert (expf m0 y y').
apply expf_symm.
tauto.
tauto.
tauto.
tauto.
intros.
rewrite nc_B in |- *.
unfold y' in |- *.
assert (y = A m zero x).
unfold y in |- *.
rewrite cA_eq in |- *.
elim (succ_dec m zero x).
tauto.
tauto.
tauto.
rewrite <- H2 in |- *.
rewrite cA_eq in |- *.
elim (succ_dec m zero x').
tauto.
intro.
generalize (disconnect_planar_criterion_B0 m x H H0 a).
simpl in |- *.
rewrite <- H2 in |- *.
intros.
elim (eqc_dec (B m zero x) x y).
elim (expf_dec m y (bottom m zero x')).
intros.
assert (bottom m zero x = bottom m zero x').
apply expe_bottom.
tauto.
unfold double_link in H1.
unfold expe in H1.
tauto.
rewrite <- H4 in a0.
tauto.
tauto.
elim (expf_dec m y (bottom m zero x')).
tauto.
intros.
assert (bottom m zero x = bottom m zero x').
apply expe_bottom.
tauto.
unfold double_link in H1.
unfold expe in H1.
tauto.
rewrite <- H4 in b1.
tauto.
tauto.
tauto.
tauto.
intro.
assert (succ m zero x').
generalize (double_link_succ m x x').
tauto.
rewrite nc_B in |- *.
assert (y' = A m zero x').
unfold y' in |- *.
rewrite cA_eq in |- *.
elim (succ_dec m zero x').
tauto.
tauto.
tauto.
rewrite <- H3 in |- *.
assert (y = bottom m zero x').
unfold y in |- *.
rewrite cA_eq in |- *.
elim (succ_dec m zero x).
tauto.
intro.
apply expe_bottom.
tauto.
unfold double_link in H1.
unfold expe in H1.
tauto.
tauto.
rewrite H4 in |- *.
generalize (disconnect_planar_criterion_B0 m x' H H0 H2).
simpl in |- *.
rewrite <- H3 in |- *.
intros.
elim (eqc_dec (B m zero x') x' y').
elim (expf_dec m (bottom m zero x') y').
intros.
assert (expf m y' (bottom m zero x')).
apply expf_symm.
tauto.
tauto.
tauto.
elim (expf_dec m (bottom m zero x') y').
tauto.
intros.
elim b0.
apply expf_symm.
tauto.
tauto.
tauto.
