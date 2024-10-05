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
tauto.
