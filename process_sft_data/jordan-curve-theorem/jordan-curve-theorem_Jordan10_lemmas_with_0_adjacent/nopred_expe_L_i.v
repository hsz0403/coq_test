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

Lemma nopred_expe_L_i: forall(m:fmap)(i:nat)(k:dim)(x y z:dart), inv_hmap (L m k x y) -> exd m z -> ~pred m zero z -> let t:= Iter (cA m zero) i z in (i < MA0.Iter_upb m z)%nat -> expe (L m k x y) z t.
Proof.
induction i.
simpl in |- *.
intros.
unfold expe in |- *.
apply MA0.expo_refl.
simpl in |- *.
tauto.
intros.
simpl in t.
unfold expe in |- *.
set (zi := Iter (cA m zero) i z) in |- *.
fold zi in t.
apply MA0.expo_trans with zi.
unfold zi in |- *.
unfold expe in IHi.
apply IHi.
tauto.
tauto.
tauto.
omega.
unfold t in |- *.
assert (t = cA (L m k x y) zero zi).
simpl in |- *.
elim (eq_dim_dec k zero).
intro.
elim (eq_dart_dec x zi).
intro.
assert (bottom m zero z = z).
apply nopred_bottom.
simpl in H.
tauto.
tauto.
tauto.
assert (bottom m zero zi = z).
rewrite <- H3 in |- *.
symmetry in |- *.
unfold zi in |- *.
apply expe_bottom_ind.
simpl in H.
tauto.
tauto.
assert (t = cA m zero zi).
unfold t in |- *.
tauto.
generalize H5.
rewrite cA_eq in |- *.
elim (succ_dec m zero zi).
rewrite <- a0 in |- *.
simpl in H.
unfold prec_L in H.
rewrite a in H.
tauto.
rewrite H4 in |- *.
unfold t in |- *.
unfold zi in |- *.
assert (Iter (cA m zero) (S i) z = cA m zero (Iter (cA m zero) i z)).
simpl in |- *.
tauto.
rewrite <- H6 in |- *.
intros.
rewrite cA0_MA0_Iter in H7.
assert (S i = 0%nat).
apply (MA0.unicity_mod_p m z (S i) 0).
simpl in H.
tauto.
tauto.
tauto.
omega.
rewrite H7 in |- *.
simpl in |- *.
tauto.
inversion H8.
simpl in H.
tauto.
intros.
elim (eq_dart_dec (cA_1 m zero y) zi).
intro.
generalize a0.
rewrite cA_1_eq in |- *.
elim (pred_dec m zero y).
simpl in H.
unfold prec_L in H.
rewrite a in H.
tauto.
intros.
assert (bottom m zero zi = y).
rewrite <- a1 in |- *.
apply bottom_top.
simpl in H.
tauto.
simpl in H.
unfold prec_L in H.
tauto.
tauto.
assert (bottom m zero y = y).
apply nopred_bottom.
simpl in H.
tauto.
simpl in H.
unfold prec_L in H.
tauto.
tauto.
assert (bottom m zero z = z).
apply nopred_bottom.
simpl in H.
tauto.
tauto.
tauto.
assert (bottom m zero z = bottom m zero zi).
unfold zi in |- *.
apply expe_bottom_ind.
simpl in H.
tauto.
tauto.
rewrite H3 in H6.
rewrite H5 in H6.
assert (t = cA m zero zi).
fold t in |- *.
tauto.
generalize H7.
rewrite cA_eq in |- *.
elim (succ_dec m zero zi).
rewrite <- a1 in |- *.
intro.
absurd (succ m zero (top m zero y)).
apply not_succ_top.
simpl in H.
tauto.
tauto.
intros.
rewrite H3 in H8.
unfold t in H8.
unfold zi in H8.
rewrite H6 in H8.
assert (cA m zero (Iter (cA m zero) i y) = Iter (cA m zero) (S i) y).
simpl in |- *.
tauto.
rewrite H9 in H8.
rewrite cA0_MA0_Iter in H8.
assert (S i = 0%nat).
apply (MA0.unicity_mod_p m y (S i) 0).
simpl in H.
tauto.
simpl in H.
unfold prec_L in H.
tauto.
rewrite <- H6 in |- *.
omega.
rewrite <- H6 in |- *.
omega.
simpl in |- *.
tauto.
inversion H10.
simpl in H.
tauto.
simpl in H.
tauto.
intros.
fold t in |- *.
tauto.
fold t in |- *.
tauto.
fold t in |- *.
rewrite H3 in |- *.
unfold MA0.expo in |- *.
split.
simpl in |- *.
unfold zi in |- *.
generalize (MA0.exd_Iter_f m i z).
simpl in H.
rewrite cA0_MA0_Iter in |- *.
tauto.
split with 1%nat.
rewrite <- cA0_MA0_Iter in |- *.
simpl in |- *.
tauto.
