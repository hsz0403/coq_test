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
tauto.
