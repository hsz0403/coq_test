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

Lemma bottom_B0_bis: forall(m:fmap)(z:dart)(i j:nat), inv_hmap m -> exd m z -> ~pred m zero z -> let zi := Iter (MA0.f m) i z in let zj := Iter (MA0.f m) j z in let m0 := B m zero zi in (i < j < MA0.Iter_upb m z)%nat -> bottom m0 zero zj = A m zero zi.
Proof.
simpl in |- *.
intros.
set (p := MA0.Iter_upb m z) in |- *.
fold p in H2.
set (zi := Iter (MA0.f m) i z) in |- *.
set (zj := Iter (MA0.f m) j z) in |- *.
set (m0 := B m zero zi) in |- *.
unfold zj in |- *.
unfold p in H2.
induction j.
absurd (i < 0 < MA0.Iter_upb m z)%nat.
omega.
tauto.
fold p in IHj.
fold p in H2.
assert (exd m zi).
unfold zi in |- *.
generalize (MA0.exd_Iter_f m i z).
tauto.
assert (exd m zj).
unfold zj in |- *.
generalize (MA0.exd_Iter_f m (S j) z).
tauto.
assert (bottom m zero z = bottom m zero zi).
apply expe_bottom.
tauto.
unfold MA0.expo in |- *.
split.
tauto.
split with i.
fold zi in |- *.
tauto.
assert (bottom m zero z = bottom m zero zj).
apply expe_bottom.
tauto.
unfold MA0.expo in |- *.
split.
tauto.
split with (S j).
fold zj in |- *.
tauto.
assert (top m zero z = top m zero zi).
apply expe_top.
tauto.
unfold MA0.expo in |- *.
split.
tauto.
split with i.
fold zi in |- *.
tauto.
assert (top m zero z = top m zero zj).
apply expe_top.
tauto.
unfold MA0.expo in |- *.
split.
tauto.
split with (S j).
fold zj in |- *.
tauto.
assert (bottom m zero z = z).
apply nopred_bottom.
tauto.
tauto.
tauto.
assert (succ m zero zi).
unfold zi in |- *.
apply succ_zi.
tauto.
tauto.
tauto.
fold p in |- *.
omega.
generalize (MA0.exd_diff_orb m z H H0).
unfold MA0.diff_orb in |- *.
unfold MA0.Iter_upb in p.
unfold MA0.Iter_upb_aux in |- *.
unfold MA0.Iter_rem in p.
fold p in |- *.
fold (MA0.Iter_rem m z) in p.
fold (MA0.Iter_upb m z) in p.
unfold MA0.diff_int in |- *.
intros.
assert (zi <> zj).
unfold zi in |- *.
unfold zj in |- *.
apply H11.
omega.
assert (z <> zj).
unfold zj in |- *.
generalize (H11 0%nat (S j)).
simpl in |- *.
intro.
apply H13.
omega.
elim (eq_nat_dec (S (S j)) p).
intro.
assert (cA m zero zj = z).
unfold zj in |- *.
assert (MA0.f m (Iter (MA0.f m) (S j) z) = Iter (MA0.f m) 1 (Iter (MA0.f m) (S j) z)).
simpl in |- *.
tauto.
assert (S (S j) = (1 + S j)%nat).
omega.
unfold p in |- *.
generalize (MA0.Iter_upb_period m z H H0).
simpl in |- *.
intro.
assert (cA m zero (MA0.f m (Iter (MA0.f m) j z)) = MA0.f m (MA0.f m (Iter (MA0.f m) j z))).
tauto.
rewrite H17 in |- *.
clear H17.
assert (MA0.f m (MA0.f m (Iter (MA0.f m) j z)) = Iter (MA0.f m) (S (S j)) z).
simpl in |- *.
tauto.
rewrite H17 in |- *.
rewrite a in |- *.
unfold p in |- *.
tauto.
assert (inv_hmap (B m zero zi)).
apply inv_hmap_B.
tauto.
assert (~ succ m zero zj).
intro.
generalize (cA_eq m zero zj H).
elim (succ_dec m zero zj).
intros.
rewrite H14 in H17.
assert (zj = A_1 m zero z).
rewrite H17 in |- *.
rewrite A_1_A in |- *.
tauto.
tauto.
tauto.
unfold pred in H1.
rewrite <- H18 in H1.
elim H1.
apply exd_not_nil with m.
tauto.
tauto.
tauto.
assert (~ succ (B m zero zi) zero zj).
unfold succ in |- *.
unfold succ in H16.
rewrite A_B_bis in |- *.
tauto.
intro.
symmetry in H17.
tauto.
assert (top m zero zi = zj).
rewrite <- H7 in |- *.
rewrite H8 in |- *.
apply nosucc_top.
tauto.
tauto.
tauto.
generalize (cA_eq m zero zj H).
elim (succ_dec m zero zj).
tauto.
intros.
generalize (cA_B m zero zi zj H H10).
elim (eq_dart_dec zi zj).
tauto.
elim (eq_dart_dec (top m zero zi) zj).
intros.
clear b a0.
generalize (cA_eq (B m zero zi) zero zj H15).
elim (succ_dec (B m zero zi) zero zj).
tauto.
intros.
fold zj in |- *.
fold m0 in H21.
fold m0 in H20.
rewrite <- H21 in |- *.
tauto.
tauto.
intro.
simpl in |- *.
set (zj' := Iter (MA0.f m) j z) in |- *.
assert (succ m zero zj).
unfold zj in |- *.
apply succ_zi.
tauto.
tauto.
tauto.
fold p in |- *.
omega.
assert (succ m zero zj').
unfold zj' in |- *.
apply succ_zi.
tauto.
tauto.
tauto.
fold p in |- *.
omega.
assert (cA m zero zj' = A m zero zj').
rewrite cA_eq in |- *.
elim (succ_dec m zero zj').
tauto.
tauto.
tauto.
assert (exd m zj').
unfold zj' in |- *.
generalize (MA0.exd_Iter_f m j z).
tauto.
assert (exd m0 zj').
unfold m0 in |- *.
generalize (exd_B m zero zi zj').
tauto.
elim (eq_nat_dec i j).
intro.
assert (zi = zj').
unfold zj' in |- *.
rewrite <- a in |- *.
fold zi in |- *.
tauto.
rewrite <- H19 in |- *.
rewrite <- H19 in H16.
assert (MA0.f m zi = cA m zero zi).
tauto.
rewrite H20 in |- *.
unfold m0 in |- *.
assert (~ pred (B m zero zi) zero (A m zero zi)).
unfold pred in |- *.
rewrite A_1_B in |- *.
tauto.
tauto.
rewrite H16 in |- *.
apply nopred_bottom.
apply inv_hmap_B.
tauto.
generalize (exd_B m zero zi (A m zero zi)).
generalize (succ_exd_A m zero zi).
tauto.
tauto.
intro.
assert (zi <> zj').
unfold zi in |- *.
unfold zj' in |- *.
apply H11.
omega.
assert (succ m0 zero zj').
unfold m0 in |- *.
unfold succ in |- *.
rewrite A_B_bis in |- *.
unfold succ in H15.
tauto.
intro.
symmetry in H20.
tauto.
assert (A m0 zero zj' = A m zero zj').
unfold m0 in |- *.
rewrite A_B_bis in |- *.
tauto.
intro.
symmetry in H21.
tauto.
assert (bottom m0 zero (A m0 zero zj') = bottom m0 zero zj').
apply bottom_A.
unfold m0 in |- *.
apply inv_hmap_B.
tauto.
tauto.
assert (cA m zero zj' = MA0.f m zj').
tauto.
rewrite <- H23 in |- *.
rewrite H16 in |- *.
rewrite <- H21 in |- *.
rewrite H22 in |- *.
unfold zj' in |- *.
apply IHj.
omega.
