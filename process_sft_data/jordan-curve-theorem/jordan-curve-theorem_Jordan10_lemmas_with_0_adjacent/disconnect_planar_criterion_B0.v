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

Theorem disconnect_planar_criterion_B0:forall (m:fmap)(x:dart), inv_hmap m -> planar m -> succ m zero x -> let y := A m zero x in let x0 := bottom m zero x in (expf m y x0 <-> ~eqc (B m zero x) x y).
Proof.
intros.
generalize (face_cut_join_criterion_B0 m x H H1).
simpl in |- *.
fold x0 in |- *.
fold y in |- *.
intros.
generalize (planarity_crit_B0 m x H H1).
simpl in |- *.
fold x0 in |- *.
fold y in |- *.
intros.
set (x_1 := cA_1 (B m zero x) one x) in |- *.
fold x_1 in H3.
assert (expf (B m zero x) x0 x_1).
assert (x0 = cA (B m zero x) zero x).
rewrite cA_B in |- *.
elim (eq_dart_dec x x).
fold x0 in |- *.
tauto.
tauto.
tauto.
tauto.
unfold x_1 in |- *.
assert (x = cA_1 (B m zero x) zero x0).
rewrite H4 in |- *.
rewrite cA_1_cA in |- *.
tauto.
apply inv_hmap_B.
tauto.
generalize (exd_B m zero x x).
assert (exd m x).
apply succ_exd with zero.
tauto.
tauto.
tauto.
set (m0 := B m zero x) in |- *.
rewrite H5 in |- *.
fold m0 in |- *.
fold (cF m0 x0) in |- *.
assert (MF.f = cF).
tauto.
rewrite <- H6 in |- *.
unfold expf in |- *.
split.
unfold m0 in |- *.
apply inv_hmap_B.
tauto.
unfold MF.expo in |- *.
split.
unfold m0 in |- *.
generalize (exd_B m zero x x0).
unfold x0 in |- *.
assert (exd m (bottom m zero x)).
apply exd_bottom.
tauto.
apply succ_exd with zero.
tauto.
tauto.
tauto.
split with 1%nat.
simpl in |- *.
tauto.
split.
intro.
intro.
assert (~ expf (B m zero x) x_1 y).
intro.
absurd (expf (B m zero x) y x0).
tauto.
apply expf_trans with x_1.
apply expf_symm.
tauto.
apply expf_symm.
tauto.
tauto.
intro.
assert (cA (B m zero x) zero x = x0).
unfold x0 in |- *.
rewrite cA_B in |- *.
elim (eq_dart_dec x x).
tauto.
tauto.
tauto.
tauto.
assert (exd m x).
apply succ_exd with zero.
tauto.
tauto.
assert (exd (B m zero x) x).
generalize (exd_B m zero x x).
tauto.
assert (inv_hmap (B m zero x)).
apply inv_hmap_B.
tauto.
generalize (eqc_cA_r (B m zero x) zero x H9 H8).
intro.
assert (~ eqc (B m zero x) y x0).
intro.
absurd (eqc (B m zero x) x y).
tauto.
apply eqc_trans with x0.
rewrite <- H6 in |- *.
tauto.
apply eqc_symm.
tauto.
assert (~ expf (B m zero x) y x0).
intro.
elim H11.
apply expf_eqc.
tauto.
unfold expf in H12.
tauto.
tauto.
