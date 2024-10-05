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

Lemma pre_ring2_Br1: forall(m:fmap)(l:list), inv_hmap m -> planar m -> double_link_list m l -> pre_ring0 m l -> pre_ring1 m l -> pre_ring2 m l -> let (x,x') := first l in let y := cA m zero x in let y' := cA m zero x' in ~expf m y y' -> pre_ring2 (Br1 m x x') (tail l).
Proof.
induction l.
simpl in |- *.
tauto.
simpl in |- *.
rename d into x.
rename d0 into x'.
simpl in |- *.
set (y := cA m zero x) in |- *.
set (y' := cA m zero x') in |- *.
intros.
decompose [and] H1.
clear H1.
decompose [and] H2.
clear H2.
induction l.
simpl in |- *.
tauto.
rename d into xs.
rename d0 into xs'.
simpl in |- *.
simpl in IHl.
induction l.
unfold face_adjacent in |- *.
clear IHl IHl0.
unfold double_link in H6.
simpl in H7.
unfold double_link in H7.
simpl in H1.
simpl in H8.
simpl in H3.
simpl in H4.
unfold face_adjacent in H3.
unfold face_adjacent in H4.
decompose [and] H3.
clear H3.
decompose [and] H6.
clear H6.
decompose [and] H7.
clear H7.
decompose [and] H8.
clear H8.
clear H1 H2 H11 H6.
fold y in H4.
fold y' in H9.
unfold expe in H7.
unfold expe in H13.
unfold expe in H10.
assert (~ MA0.expo m x xs').
intro.
apply H7.
apply MA0.expo_trans with xs'.
tauto.
apply MA0.expo_symm.
tauto.
tauto.
assert (~ MA0.expo m x' xs').
intro.
apply H1.
apply MA0.expo_trans with x'.
tauto.
tauto.
assert (~ MA0.expo m x' xs).
intro.
apply H7.
apply MA0.expo_trans with x'.
tauto.
tauto.
rewrite cA0_Br1 in |- *.
elim (eq_dart_dec x xs').
intro.
rewrite <- a in H1.
elim H1.
apply MA0.expo_refl.
unfold MA0.expo in H10.
tauto.
elim (eq_dart_dec x' xs').
intro.
rewrite <- a in H1.
tauto.
intros.
rewrite cA0_Br1 in |- *.
elim (eq_dart_dec x xs).
intro.
rewrite <- a in H7.
elim H7.
apply MA0.expo_refl.
unfold MA0.expo in H10.
tauto.
elim (eq_dart_dec x' xs).
intros.
rewrite <- a in H7.
tauto.
intros.
unfold Br1 in |- *.
elim (succ_dec m zero x).
elim (succ_dec m zero x').
intros.
set (m0 := L (B m zero x) zero (top m zero x) (bottom m zero x)) in |- *.
assert (y = bottom m0 zero x').
unfold m0 in |- *.
assert (exd m x').
apply MA0.expo_exd with x.
tauto.
tauto.
rewrite (bottom_L_B_top_bot m x x' H a0 H8 H3) in |- *.
elim (MA0.expo_dec m x x' H).
intro.
unfold y in |- *.
rewrite cA_eq in |- *.
elim (succ_dec m zero x).
tauto.
tauto.
tauto.
tauto.
assert (y' = A m0 zero x').
unfold m0 in |- *.
rewrite (A_L_B_top_bot m zero x x' H a0) in |- *.
elim (eq_dart_dec x x').
tauto.
elim (eq_dart_dec (top m zero x) x').
intros.
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
assert (~ expf m0 y y').
intro.
apply H5.
generalize (expf_L_B_top_bot m zero x y y' H a0).
fold m0 in |- *.
tauto.
assert (expf m0 (cA m zero xs') y).
generalize (expf_L_B_top_bot m zero x (cA m zero xs') y H a0).
fold m0 in |- *.
tauto.
assert (expf m0 y' (cA m zero xs)).
generalize (expf_L_B_top_bot m zero x y' (cA m zero xs) H a0).
fold m0 in |- *.
tauto.
assert (~ expf m0 (A m0 zero x') (bottom m0 zero x')).
rewrite <- H11 in |- *.
rewrite <- H8 in |- *.
intro.
apply H14.
apply expf_symm.
tauto.
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
generalize (face_cut_join_criterion_B0 m0 x' H18 H19).
intros.
assert (expf (B m0 zero x') (A m0 zero x') (bottom m0 zero x')).
elim (expf_dec (B m0 zero x') (A m0 zero x') (bottom m0 zero x')).
tauto.
intro.
simpl in H20.
simpl in b3.
simpl in H17.
tauto.
assert (expf (B m0 zero x') (cA m zero xs') y).
apply expf_expf_B.
tauto.
tauto.
tauto.
tauto.
assert (expf (B m0 zero x') y' (cA m zero xs)).
apply expf_expf_B.
tauto.
tauto.
tauto.
tauto.
rewrite <- H11 in H21.
rewrite <- H8 in H21.
apply expf_trans with y.
tauto.
apply expf_trans with y'.
apply expf_symm.
tauto.
tauto.
intros.
assert (y' = bottom m zero x).
unfold y' in |- *.
rewrite cA_eq in |- *.
elim (succ_dec m zero x').
tauto.
symmetry in |- *.
apply expe_bottom.
tauto.
tauto.
tauto.
unfold y in H5.
rewrite H8 in H5.
apply expf_B0_CS.
tauto.
tauto.
elim (expf_dec m (cA m zero x) (bottom m zero x)).
tauto.
intro.
fold y in |- *.
assert (expf m y (cA m zero xs')).
apply expf_symm.
tauto.
rewrite <- H8 in |- *.
fold y in |- *.
tauto.
intro.
assert (y = bottom m zero x').
unfold y in |- *.
rewrite cA_eq in |- *.
elim (succ_dec m zero x).
tauto.
intro.
apply expe_bottom.
tauto.
tauto.
tauto.
rewrite H8 in H5.
unfold y' in H5.
apply expf_B0_CS.
tauto.
generalize (double_link_succ m x x').
unfold double_link in |- *.
unfold expe in |- *.
tauto.
elim (expf_dec m (cA m zero x') (bottom m zero x')).
intro.
elim H5.
apply expf_symm.
tauto.
intro.
fold y' in |- *.
rewrite <- H8 in |- *.
assert (expf m y (cA m zero xs')).
apply expf_symm.
tauto.
tauto.
tauto.
unfold double_link in |- *; unfold expe in |- *.
tauto.
tauto.
unfold double_link in |- *; unfold expe in |- *.
tauto.
rename d into xf.
rename d0 into xf'.
clear IHl IHl0 IHl1.
assert (last (cons xs xs' (cons xf xf' l)) = last (cons xf xf' l)).
simpl in |- *.
tauto.
rewrite H2 in H4.
decompose [and] H3.
clear H3.
generalize H4 H10.
unfold face_adjacent in |- *.
set (m1 := Br1 m x x') in |- *.
assert (let (_, xs'0) := last (cons xf xf' l) in x <> xs'0 /\ x' <> xs'0).
apply distinct_last_darts with m.
tauto.
simpl in |- *.
simpl in H7.
tauto.
simpl in |- *.
simpl in H1.
simpl in H8.
tauto.
generalize H3.
clear H3.
simpl in H8.
assert (x <> xs /\ x' <> xs).
unfold double_link in H6.
unfold expe in H6.
assert (~ MA0.expo m x' xs).
intro.
absurd (expe m x xs).
tauto.
unfold expe in |- *.
apply MA0.expo_trans with x'.
tauto.
tauto.
unfold expe in H8.
split.
intro.
rewrite <- H11 in H8.
absurd (MA0.expo m x x).
tauto.
apply MA0.expo_refl.
unfold MA0.expo in H6.
tauto.
intro.
rewrite <- H11 in H3.
apply H3.
apply MA0.expo_refl.
apply MA0.expo_exd with x.
tauto.
tauto.
generalize (last (cons xf xf' l)).
intro.
elim p.
intros.
rename b into xs'0.
assert (cA m1 zero xs'0 = cA m zero xs'0).
unfold m1 in |- *.
rewrite cA0_Br1 in |- *.
elim (eq_dart_dec x xs'0).
tauto.
elim (eq_dart_dec x' xs'0).
tauto.
tauto.
tauto.
tauto.
assert (cA m1 zero xs = cA m zero xs).
unfold m1 in |- *.
rewrite cA0_Br1 in |- *.
elim (eq_dart_dec x xs).
tauto.
elim (eq_dart_dec x' xs).
tauto.
tauto.
tauto.
tauto.
rewrite H14 in |- *.
rewrite H15 in |- *.
assert (expf m1 (cA m zero x) (cA m zero x')).
unfold m1 in |- *.
apply expf_Br1_link.
tauto.
tauto.
tauto.
fold y in |- *.
fold y' in |- *.
tauto.
assert (expf m1 (cA m zero xs'0) (cA m zero x)).
unfold m1 in |- *.
apply expf_Br1.
tauto.
tauto.
tauto.
tauto.
tauto.
assert (expf m1 (cA m zero x') (cA m zero xs)).
unfold m1 in |- *.
apply expf_Br1.
tauto.
tauto.
tauto.
tauto.
tauto.
apply expf_trans with (cA m zero x).
tauto.
apply expf_trans with (cA m zero x').
tauto.
tauto.
