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

Theorem disconnect_planar_criterion_Br1: forall (m:fmap)(x x':dart), inv_hmap m -> planar m -> double_link m x x' -> let y := cA m zero x in let y' := cA m zero x' in (expf m y y' <-> ~eqc (Br1 m x x') x' y').
Proof.
intros.
rename H1 into DL.
unfold Br1 in |- *.
elim (succ_dec m zero x).
elim (succ_dec m zero x').
intros.
set (m0 := L (B m zero x) zero (top m zero x) (bottom m zero x)) in |- *.
assert (eqc m0 x' y' <-> eqc m x' y').
unfold m0 in |- *.
apply (eqc_L_B_top_bot m zero x x' y' H a0).
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
unfold double_link in DL.
tauto.
elim (eq_dart_dec (top m zero x) x').
intro.
rewrite <- a1 in a.
absurd (succ m zero (top m zero x)).
apply not_succ_top.
tauto.
tauto.
unfold succ in a.
tauto.
tauto.
tauto.
generalize (eqc_B m0 zero x' x' y' H2 H3).
intros.
assert (planar m0).
unfold m0 in |- *.
apply planar_L_B_top_bot_0.
tauto.
tauto.
tauto.
generalize (disconnect_planar_criterion_B0 m0 x' H2 H5 H3).
intros.
generalize (expf_L_B_top_bot m zero x y y' H a0).
fold m0 in |- *.
intro.
set (x0 := bottom m0 zero x') in |- *.
assert (exd m x').
apply succ_exd with zero.
tauto.
tauto.
assert (x <> x').
unfold double_link in DL.
tauto.
generalize (bottom_L_B_top_bot m x x' H a0 H8 H9).
fold m0 in |- *.
elim (MA0.expo_dec m x x' H).
intro.
intro.
assert (cA m zero x = A m zero x).
rewrite cA_eq in |- *.
elim (succ_dec m zero x).
tauto.
tauto.
tauto.
fold y in H11.
assert (A m0 zero x' = y').
unfold m0 in |- *.
rewrite A_L_B_top_bot in |- *.
elim (eq_dart_dec x x').
unfold double_link in DL.
tauto.
elim (eq_dart_dec (top m zero x) x').
intro.
rewrite <- a2 in a.
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
unfold m0 in H10.
fold m0 in H10.
unfold y in H6.
rewrite H12 in H6.
rewrite H10 in H6.
rewrite <- H11 in H6.
assert (expf m y y' <-> expf m y' y).
split.
apply expf_symm.
apply expf_symm.
assert (expf m0 y y' <-> expf m0 y' y).
split.
apply expf_symm.
apply expf_symm.
tauto.
intros.
unfold m0 in H10.
unfold double_link in DL.
unfold expe in DL.
tauto.
intros.
assert (y' = bottom m zero x').
unfold y' in |- *.
rewrite cA_eq in |- *.
elim (succ_dec m zero x').
tauto.
tauto.
tauto.
generalize (expe_bottom m x x' H).
intro.
rewrite <- H2 in H1.
rewrite H1 in |- *.
assert (top m zero x' = x').
rewrite nosucc_top in |- *.
tauto.
tauto.
unfold double_link in DL.
apply MA0.expo_exd with x.
tauto.
unfold expe in DL.
tauto.
tauto.
generalize (expe_top m x x' H).
intro.
rewrite <- H3 in |- *.
rewrite <- H4 in |- *.
set (x0 := bottom m zero x) in |- *.
set (h0 := top m zero x) in |- *.
generalize (eqc_B_top m zero x H a).
intro.
assert (exd m x).
apply succ_exd with zero.
tauto.
tauto.
generalize (eqc_B_bottom m zero x H H6).
intro.
generalize (disconnect_planar_criterion_B0 m x H H0 a).
simpl in |- *.
intros.
assert (y = A m zero x).
unfold y in |- *.
rewrite cA_eq in |- *.
elim (succ_dec m zero x).
tauto.
tauto.
tauto.
rewrite <- H9 in H8.
fold x0 in H7.
fold x0 in H8.
fold h0 in H5.
rewrite <- H9 in H5.
assert (~ eqc (B m zero x) h0 x0 <-> ~ eqc (B m zero x) x y).
split.
intro.
intro.
apply H10.
clear H10.
apply eqc_trans with x.
apply eqc_symm.
apply eqc_trans with y.
tauto.
tauto.
tauto.
intro.
intro.
apply H10.
clear H10.
apply eqc_trans with x0.
tauto.
apply eqc_trans with h0.
apply eqc_symm.
tauto.
apply eqc_symm.
tauto.
tauto.
unfold double_link in DL.
unfold expe in DL.
tauto.
unfold double_link in DL.
unfold expe in DL.
tauto.
intros.
assert (y = bottom m zero x).
unfold y in |- *.
rewrite cA_eq in |- *.
elim (succ_dec m zero x).
tauto.
tauto.
tauto.
assert (y = bottom m zero x').
rewrite H1 in |- *.
apply expe_bottom.
tauto.
unfold double_link in DL.
unfold expe in DL.
tauto.
rewrite H2 in |- *.
elim (succ_dec m zero x').
intro.
generalize (disconnect_planar_criterion_B0 m x' H H0 a).
simpl in |- *.
intro.
assert (expf m (bottom m zero x') y' <-> expf m (A m zero x') (bottom m zero x')).
assert (y' = A m zero x').
unfold y' in |- *.
rewrite cA_eq in |- *.
elim (succ_dec m zero x').
tauto.
tauto.
tauto.
rewrite <- H4 in |- *.
split.
apply expf_symm.
apply expf_symm.
assert (y' = A m zero x').
unfold y' in |- *.
rewrite cA_eq in |- *.
elim (succ_dec m zero x').
tauto.
tauto.
tauto.
rewrite <- H5 in H4.
rewrite <- H5 in H3.
tauto.
intro.
unfold double_link in DL.
unfold expe in DL.
assert (exd m x').
apply MA0.expo_exd with x.
tauto.
tauto.
elim DL.
clear DL.
intros.
assert (exd m x).
unfold MA0.expo in H5.
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
elim H4.
rewrite <- H7 in |- *.
rewrite <- H8 in |- *.
apply expe_top.
tauto.
tauto.
