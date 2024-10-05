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

Lemma cA0_MA0:forall(m:fmap)(z:dart), cA m zero z = MA0.f m z.
Proof.
Admitted.

Lemma cA0_MA0_Iter:forall(m:fmap)(i:nat)(z:dart), Iter (cA m zero) i z = Iter (MA0.f m) i z.
Proof.
induction i.
simpl in |- *.
tauto.
intros.
simpl in |- *.
rewrite IHi in |- *.
rewrite cA0_MA0 in |- *.
Admitted.

Lemma bottom_cA: forall(m:fmap)(k:dim)(z:dart), inv_hmap m -> exd m z -> bottom m k (cA m k z) = bottom m k z.
Proof.
induction m.
simpl in |- *.
tauto.
simpl in |- *.
unfold prec_I in |- *.
intros.
elim (eq_dart_dec d z).
elim (eq_dart_dec d z).
tauto.
tauto.
elim (eq_dart_dec d (cA m k z)).
intros.
rewrite a in H.
absurd (exd m (cA m k z)).
tauto.
generalize (exd_cA m k z).
tauto.
intros.
apply IHm.
tauto.
tauto.
simpl in |- *.
unfold prec_L in |- *.
unfold succ in |- *.
unfold pred in |- *.
intros.
decompose [and] H.
clear H.
elim (eq_dim_dec d k).
intro.
rewrite <- a in |- *.
elim (eq_dart_dec d0 z).
intro.
elim (eq_dart_dec d1 (bottom m d d1)).
intro.
elim (eq_dart_dec d1 (bottom m d z)).
tauto.
rewrite a0 in |- *.
tauto.
intro.
elim b.
symmetry in |- *.
apply nopred_bottom.
tauto.
tauto.
unfold pred in |- *.
tauto.
elim (eq_dart_dec (cA_1 m d d1) z).
elim (eq_dart_dec d1 (bottom m d (cA m d d0))).
intros.
rewrite IHm in a0.
generalize H7.
rewrite cA_eq in |- *.
elim (succ_dec m d d0).
unfold succ in |- *.
tauto.
symmetry in a0.
tauto.
tauto.
tauto.
tauto.
intros.
elim (eq_dart_dec d1 (bottom m d z)).
intros.
apply IHm.
tauto.
tauto.
intro.
rewrite cA_1_eq in a0.
generalize a0.
elim (pred_dec m d d1).
unfold pred in |- *.
tauto.
intros.
rewrite <- a1 in b1.
rewrite bottom_top in b1.
tauto.
tauto.
tauto.
unfold pred in |- *.
tauto.
tauto.
elim (eq_dart_dec d1 (bottom m d (cA m d z))).
intros.
rewrite IHm in a0.
elim (eq_dart_dec d1 (bottom m d z)).
tauto.
intros.
tauto.
tauto.
tauto.
rewrite IHm in |- *.
intros.
elim (eq_dart_dec d1 (bottom m d z)).
tauto.
tauto.
tauto.
tauto.
rewrite IHm in |- *.
tauto.
tauto.
Admitted.

Lemma expe_bottom_ind: forall(m:fmap)(z:dart)(i:nat), inv_hmap m -> exd m z -> let t:= Iter (cA m zero) i z in bottom m zero z = bottom m zero t.
Proof.
induction i.
simpl in |- *.
tauto.
simpl in IHi.
simpl in |- *.
intros.
rewrite bottom_cA in |- *.
apply IHi.
tauto.
tauto.
tauto.
generalize (MA0.exd_Iter_f m i z).
rewrite cA0_MA0_Iter in |- *.
Admitted.

Lemma expe_bottom: forall(m:fmap)(z t:dart), inv_hmap m -> MA0.expo m z t -> bottom m zero z = bottom m zero t.
Proof.
intros.
unfold MA0.expo in H0.
elim H0.
intros.
elim H2.
intros i Hi.
rewrite <- Hi in |- *.
rewrite <- cA0_MA0_Iter in |- *.
apply expe_bottom_ind.
tauto.
Admitted.

Lemma top_cA_1: forall(m:fmap)(k:dim)(z:dart), inv_hmap m -> exd m z -> top m k (cA_1 m k z) = top m k z.
Proof.
induction m.
simpl in |- *.
tauto.
simpl in |- *.
unfold prec_I in |- *.
intros.
elim (eq_dart_dec d z).
elim (eq_dart_dec d z).
tauto.
tauto.
elim (eq_dart_dec d (cA_1 m k z)).
intros.
rewrite a in H.
absurd (exd m (cA_1 m k z)).
tauto.
generalize (exd_cA_1 m k z).
tauto.
intros.
apply IHm.
tauto.
tauto.
simpl in |- *.
unfold prec_L in |- *.
unfold succ in |- *.
unfold pred in |- *.
intros.
decompose [and] H.
clear H.
elim (eq_dim_dec d k).
intro.
rewrite <- a in |- *.
elim (eq_dart_dec d1 z).
intro.
elim (eq_dart_dec d0 (top m d d0)).
intro.
elim (eq_dart_dec d0 (top m d z)).
tauto.
rewrite a0 in |- *.
tauto.
intro.
elim b.
symmetry in |- *.
apply nosucc_top.
tauto.
tauto.
unfold succ in |- *.
tauto.
elim (eq_dart_dec (cA m d d0) z).
elim (eq_dart_dec d0 (top m d (cA_1 m d d1))).
intros.
rewrite IHm in a0.
generalize H7.
intro.
assert (d0 <> cA_1 m d d1).
intro.
rewrite H in H6.
rewrite cA_cA_1 in H6.
tauto.
tauto.
tauto.
generalize H.
rewrite cA_1_eq in |- *.
elim (pred_dec m d d1).
unfold pred in |- *.
tauto.
tauto.
tauto.
tauto.
tauto.
intros.
elim (eq_dart_dec d0 (top m d z)).
intros.
apply IHm.
tauto.
tauto.
intro.
rewrite cA_eq in a0.
generalize a0.
elim (succ_dec m d d0).
unfold succ in |- *.
tauto.
intros.
rewrite <- a1 in b1.
rewrite top_bottom in b1.
tauto.
tauto.
tauto.
unfold succ in |- *.
tauto.
tauto.
elim (eq_dart_dec d0 (top m d (cA_1 m d z))).
intros.
rewrite IHm in a0.
elim (eq_dart_dec d0 (top m d z)).
tauto.
intros.
tauto.
tauto.
tauto.
rewrite IHm in |- *.
intros.
elim (eq_dart_dec d0 (top m d z)).
tauto.
tauto.
tauto.
tauto.
rewrite IHm in |- *.
tauto.
tauto.
Admitted.

Lemma cA0_1_MA0_1:forall(m:fmap)(z:dart), cA_1 m zero z = MA0.f_1 m z.
Proof.
Admitted.

Lemma cA0_1_MA0_1_Iter:forall(m:fmap)(i:nat)(z:dart), Iter (cA_1 m zero) i z = Iter (MA0.f_1 m) i z.
Proof.
induction i.
simpl in |- *.
tauto.
intros.
simpl in |- *.
rewrite IHi in |- *.
rewrite cA0_1_MA0_1 in |- *.
Admitted.

Lemma expe_top_ind: forall(m:fmap)(z:dart)(i:nat), inv_hmap m -> exd m z -> let t:= Iter (cA m zero) i z in top m zero z = top m zero t.
Proof.
intros.
assert (z = Iter (cA_1 m zero) i t).
unfold t in |- *.
rewrite cA0_MA0_Iter in |- *.
rewrite cA0_1_MA0_1_Iter in |- *.
rewrite MA0.Iter_f_f_1_i in |- *.
tauto.
tauto.
tauto.
induction i.
simpl in |- *.
tauto.
simpl in IHi.
generalize IHi.
clear IHi.
rewrite cA0_MA0_Iter in |- *.
rewrite cA0_1_MA0_1_Iter in |- *.
rewrite MA0.Iter_f_f_1_i in |- *.
rewrite <- cA0_MA0_Iter in |- *.
fold t in |- *.
intros.
assert (top m zero z = top m zero (Iter (cA m zero) i z)).
tauto.
clear H1.
simpl in t.
assert (cA_1 m zero t = Iter (cA m zero) i z).
unfold t in |- *.
rewrite cA_1_cA in |- *.
tauto.
tauto.
generalize (MA0.exd_Iter_f m i z).
rewrite cA0_MA0_Iter in |- *.
tauto.
rewrite <- H1 in H2.
rewrite H2 in |- *.
apply top_cA_1.
tauto.
unfold t in |- *.
generalize (exd_cA m zero (Iter (cA m zero) i z)).
generalize (MA0.exd_Iter_f m i z).
rewrite cA0_MA0 in |- *.
rewrite cA0_MA0_Iter in |- *.
tauto.
tauto.
Admitted.

Lemma expe_top: forall(m:fmap)(z t:dart), inv_hmap m -> MA0.expo m z t -> top m zero z = top m zero t.
Proof.
intros.
unfold MA0.expo in H0.
elim H0.
intros.
elim H2.
intros i Hi.
rewrite <- Hi in |- *.
rewrite <- cA0_MA0_Iter in |- *.
apply expe_top_ind.
tauto.
Admitted.

Lemma bottom_B0: forall(m:fmap)(z:dart), inv_hmap m -> exd m z -> bottom (B m zero z) zero z = bottom m zero z.
Proof.
intros.
assert (inv_hmap (B m zero z)).
apply inv_hmap_B.
tauto.
generalize (cA_eq (B m zero z) zero z H1).
intro.
elim (succ_dec m zero z).
intro.
generalize (cA_B m zero z z H a).
elim (eq_dart_dec z z).
intros.
generalize H2.
elim (succ_dec (B m zero z) zero z).
unfold succ in |- *.
rewrite A_B.
tauto.
tauto.
intros.
rewrite H4 in H3.
tauto.
tauto.
intro.
rewrite not_succ_B.
tauto.
tauto.
Admitted.

Lemma succ_zi: forall(m:fmap)(z:dart)(i:nat), inv_hmap m -> exd m z -> ~pred m zero z -> (i + 1 < MA0.Iter_upb m z)%nat -> let zi:= Iter (MA0.f m) i z in succ m zero zi.
Proof.
intros.
assert (exd m zi).
unfold zi in |- *.
generalize (MA0.exd_Iter_f m i z).
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
assert (top m zero z = top m zero zi).
apply expe_top.
tauto.
unfold MA0.expo in |- *.
split.
tauto.
split with i.
fold zi in |- *.
tauto.
assert (bottom m zero z = z).
apply nopred_bottom.
tauto.
tauto.
tauto.
generalize (succ_dec m zero zi).
intro.
elim H7.
tauto.
intro.
assert (top m zero zi = zi).
apply nosucc_top.
tauto.
tauto.
tauto.
generalize (cA_eq m zero zi H).
elim (succ_dec m zero zi).
tauto.
intros.
rewrite <- H4 in H9.
rewrite H6 in H9.
assert (cA m zero zi = MA0.f m zi).
tauto.
rewrite H10 in H9.
unfold zi in H9.
assert (Iter (MA0.f m) (S i) z = z).
simpl in |- *.
tauto.
assert (S i = 0%nat).
apply (MA0.unicity_mod_p m z (S i) 0).
tauto.
tauto.
omega.
omega.
simpl in |- *.
tauto.
Admitted.

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
Admitted.

Lemma bottom_B0_ter: forall(m:fmap)(z:dart)(i j:nat), inv_hmap m -> exd m z -> ~pred m zero z -> let zi := Iter (MA0.f m) i z in let zj := Iter (MA0.f m) j z in let m0 := B m zero zi in (j <= i < MA0.Iter_upb m z)%nat -> bottom m0 zero zj = bottom m zero zj.
Proof.
intros.
elim (succ_dec m zero zi).
intro Szi.
set (p := MA0.Iter_upb m z) in |- *.
fold p in H2.
unfold zj in |- *.
unfold p in H2.
induction j.
simpl in |- *.
simpl in zj.
assert (~ pred m0 zero z).
unfold pred in |- *.
unfold m0 in |- *.
rewrite A_1_B_bis in |- *.
unfold pred in H1.
tauto.
tauto.
intro.
unfold pred in H1.
rewrite H3 in H1.
rewrite A_1_A in H1.
generalize (MA0.exd_Iter_f m i z).
fold zi in |- *.
intros.
apply H1.
apply exd_not_nil with m.
tauto.
tauto.
tauto.
unfold succ in |- *.
rewrite <- H3 in |- *.
apply exd_not_nil with m.
tauto.
tauto.
rewrite nopred_bottom in |- *.
rewrite nopred_bottom in |- *.
tauto.
tauto.
tauto.
tauto.
unfold m0 in |- *.
apply inv_hmap_B.
tauto.
unfold m0 in |- *.
generalize (exd_B m zero zi z).
tauto.
tauto.
assert (j < i)%nat.
omega.
simpl in |- *.
rename zj into zj1.
set (zj := Iter (MA0.f m) j z) in |- *.
rewrite <- cA0_MA0 in |- *.
assert (exd m zj).
unfold zj in |- *.
generalize (MA0.exd_Iter_f m j z).
tauto.
rewrite bottom_cA in |- *.
assert (cA m0 zero zj = cA m zero zj).
unfold m0 in |- *.
rewrite cA_B in |- *.
elim (eq_dart_dec zi zj).
intro.
assert (i = j).
apply (MA0.unicity_mod_p m z i j H H0).
tauto.
omega.
fold zi in |- *.
fold zj in |- *.
tauto.
absurd (i = j).
omega.
tauto.
intro.
elim (eq_dart_dec (top m zero zi) zj).
intro.
assert (bottom m zero z = z).
apply nopred_bottom.
tauto.
tauto.
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
assert (bottom m zero z = bottom m zero zj1).
apply expe_bottom.
tauto.
unfold MA0.expo in |- *.
split.
tauto.
split with (S j).
fold zj1 in |- *.
tauto.
assert (bottom m zero z = bottom m zero zj).
apply expe_bottom.
tauto.
unfold MA0.expo in |- *.
split.
tauto.
split with j.
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
tauto.
assert (top m zero z = top m zero zj1).
apply expe_top.
tauto.
unfold MA0.expo in |- *.
split.
tauto.
split with (S j).
fold zj1 in |- *.
tauto.
assert (z = zj1).
rewrite <- H5 in |- *.
rewrite H6 in |- *.
rewrite <- cA_top in |- *.
rewrite a in |- *.
unfold zj1 in |- *.
simpl in |- *.
fold zj in |- *.
rewrite cA0_MA0 in |- *.
tauto.
tauto.
unfold zi in |- *.
generalize (MA0.exd_Iter_f m i z).
tauto.
assert (0%nat = S j).
apply (MA0.unicity_mod_p m z 0 (S j) H H0).
omega.
omega.
simpl in |- *.
unfold zj1 in H9.
simpl in H9.
tauto.
inversion H10.
tauto.
tauto.
tauto.
rewrite <- H5 in |- *.
rewrite bottom_cA in |- *.
unfold zj in |- *.
apply IHj.
omega.
unfold m0 in |- *.
apply inv_hmap_B.
tauto.
unfold m0 in |- *.
generalize (exd_B m zero zi zj).
tauto.
tauto.
tauto.
intro.
unfold m0 in |- *.
rewrite not_succ_B in |- *.
tauto.
tauto.
Admitted.

Lemma bottom_B0_quad: forall(m:fmap)(z v:dart)(j:nat), inv_hmap m -> exd m z -> ~pred m zero z -> let m0 := B m zero v in let t := Iter (MA0.f m) j z in (j < MA0.Iter_upb m z)%nat -> ~MA0.expo m z v -> bottom m0 zero t = bottom m zero t.
Proof.
intros.
elim (succ_dec m zero v).
intro.
assert (inv_hmap m0).
unfold m0 in |- *.
apply inv_hmap_B.
tauto.
assert (~ pred m0 zero z).
unfold m0 in |- *.
elim (eq_nat_dec z (A m zero v)).
intro.
unfold pred in |- *.
rewrite a0.
rewrite A_1_B.
tauto.
tauto.
intro.
unfold pred in |- *.
rewrite A_1_B_bis.
unfold pred in H1.
tauto.
tauto.
tauto.
induction j.
simpl in t.
unfold t in |- *.
rewrite nopred_bottom.
rewrite nopred_bottom.
tauto.
tauto.
tauto.
tauto.
tauto.
unfold m0 in |- *.
generalize (exd_B m zero v z).
tauto.
tauto.
set (t' := Iter (MA0.f m) j z) in |- *.
assert (t' <> v).
unfold MA0.expo in H3.
assert (~ (exists i : nat, Iter (MA0.f m) i z = v)).
tauto.
clear H3.
unfold t' in |- *.
intro.
elim H6.
split with j.
tauto.
assert (succ m zero t').
unfold t' in |- *.
apply succ_zi.
tauto.
tauto.
tauto.
omega.
assert (A m0 zero t' = A m zero t').
unfold m0 in |- *.
rewrite A_B_bis.
tauto.
tauto.
assert (cA m zero t' = A m zero t').
rewrite cA_eq.
elim (succ_dec m zero t').
tauto.
tauto.
tauto.
assert (succ m0 zero t').
unfold succ in |- *.
unfold m0 in |- *.
rewrite A_B_bis.
unfold succ in H7.
tauto.
tauto.
assert (cA m0 zero t' = A m0 zero t').
rewrite cA_eq.
elim (succ_dec m0 zero t').
tauto.
tauto.
tauto.
assert (t = cA m zero t').
unfold t' in |- *.
assert (cA m zero (Iter (MA0.f m) j z) = MA0.f m (Iter (MA0.f m) j z)).
tauto.
rewrite H12 in |- *.
clear H12.
unfold t in |- *.
simpl in |- *.
tauto.
rewrite H12.
rewrite H9.
rewrite bottom_A.
rewrite <- H8.
rewrite bottom_A.
unfold t' in |- *.
apply IHj.
omega.
tauto.
tauto.
tauto.
tauto.
unfold m0 in |- *.
intro.
rewrite not_succ_B.
tauto.
tauto.
Admitted.

Lemma not_between_B0:forall(m:fmap)(x z:dart), inv_hmap m -> exd m x -> exd m z -> x <> z -> let z0:= bottom m zero z in ~betweene m z0 x z -> (~MA0.expo m z0 x \/ forall(i j:nat), x = Iter (MA0.f m) i z0 -> z = Iter (MA0.f m) j z0 -> (i < MA0.Iter_upb m z0)%nat -> (j < MA0.Iter_upb m z0)%nat -> (j <= i)%nat).
Proof.
intros.
unfold betweene in |- *.
elim (MA0.expo_dec m z0 x).
intro.
right.
unfold betweene in H3.
unfold MA0.between in H3.
intros.
elim (le_gt_dec j i).
tauto.
intro.
elim H3.
intros.
clear H3.
split with i.
split with j.
split.
symmetry in |- *.
tauto.
split.
symmetry in |- *.
tauto.
elim (eq_nat_dec i j).
intro.
rewrite a0 in H4.
rewrite <- H5 in H4.
tauto.
intro.
omega.
tauto.
Admitted.

Lemma Iter_cA0_I: forall(m:fmap)(d z:dart)(t:tag)(p:point)(i:nat), inv_hmap (I m d t p) -> exd m z -> Iter (cA (I m d t p) zero) i z = Iter (cA m zero) i z.
Proof.
induction i.
simpl in |- *.
tauto.
intros.
set (x := cA (I m d t p) zero) in |- *.
simpl in |- *.
unfold x in |- *.
rewrite IHi in |- *.
simpl in |- *.
elim (eq_dart_dec d (Iter (cA m zero) i z)).
intro.
rewrite cA0_MA0_Iter in a.
generalize (MA0.exd_Iter_f m i z).
rewrite <- a in |- *.
simpl in H.
unfold prec_I in H.
tauto.
tauto.
tauto.
Admitted.

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
Admitted.

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

Lemma betweene_dec1: forall(m:fmap)(z v t:dart), inv_hmap m -> exd m z -> exd m v -> (betweene m z v t \/ ~betweene m z v t).
Proof.
intros.
generalize (MA0.expo_dec m z v H).
generalize (MA0.expo_dec m z t H).
intros.
intros.
elim H3.
clear H3.
elim H2.
clear H2.
intros.
generalize (MA0.expo_expo1 m z v H).
generalize (MA0.expo_expo1 m z t H).
intros.
assert (MA0.expo1 m z v).
tauto.
assert (MA0.expo1 m z t).
tauto.
clear H2 H3.
unfold MA0.expo1 in H4.
unfold MA0.expo1 in H5.
decompose [and] H4.
decompose [and] H5.
clear H4 H5.
elim H3.
intros i Hi.
elim H7.
intros j Hj.
clear H3 H7.
decompose [and] Hj.
clear Hj.
decompose [and] Hi.
clear Hi.
elim (le_gt_dec i j).
intro.
left.
unfold betweene in |- *.
unfold MA0.between in |- *.
intros.
split with i.
split with j.
split.
tauto.
split.
tauto.
omega.
intro.
right.
unfold betweene in |- *.
unfold MA0.between in |- *.
intro.
assert (exists i : nat, (exists j : nat, Iter (MA0.f m) i z = v /\ Iter (MA0.f m) j z = t /\ (i <= j < MA0.Iter_upb m z)%nat)).
tauto.
clear H8.
elim H9.
intros i' Hi'.
clear H9.
elim Hi'.
intros j' Hj'.
decompose [and] Hj'.
clear Hj'.
clear Hi'.
set (p := MA0.Iter_upb m z) in |- *.
fold p in H3.
fold p in H5.
fold p in H12.
assert (i' = i).
apply (MA0.unicity_mod_p m z i' i H H6).
fold p in |- *.
omega.
fold p in |- *.
omega.
rewrite H7.
tauto.
assert (j' = j).
apply (MA0.unicity_mod_p m z j' j H H6).
fold p in |- *.
omega.
fold p in |- *.
omega.
rewrite H4.
tauto.
absurd (i' = i).
omega.
tauto.
clear H2.
intros.
right.
intro.
unfold betweene in H2.
generalize (MA0.between_expo m z v t H H0 H2).
tauto.
clear H3.
elim H2.
intros.
clear H2.
right.
intro.
unfold betweene in H2.
generalize (MA0.between_expo m z v t H H0 H2).
tauto.
clear H2.
intros.
right.
intro.
unfold betweene in H2.
generalize (MA0.between_expo m z v t H H0 H2).
tauto.
