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

Lemma nc_L_B_top_bot :forall(m:fmap)(k:dim)(x:dart), inv_hmap m -> succ m k x -> let m0:= L (B m k x) k (top m k x) (bottom m k x) in nc m0 = nc m.
Proof.
simpl in |- *.
intros.
rewrite nc_B in |- *.
assert (exd m x).
apply succ_exd with k.
tauto.
tauto.
generalize (eqc_B_top m k x H H0).
generalize (eqc_B_bottom m k x H H1).
intros.
elim (eqc_dec (B m k x) x (A m k x)).
elim (eqc_dec (B m k x) (top m k x) (bottom m k x)).
intros.
omega.
intros.
elim b.
apply eqc_trans with (A m k x).
apply eqc_symm.
tauto.
apply eqc_trans with x.
apply eqc_symm.
tauto.
tauto.
elim (eqc_dec (B m k x) (top m k x) (bottom m k x)).
intros.
elim b.
apply eqc_trans with (bottom m k x).
tauto.
apply eqc_trans with (top m k x).
apply eqc_symm.
tauto.
apply eqc_symm.
tauto.
intros.
omega.
tauto.
Admitted.

Lemma eqc_L_B_top_bot:forall (m:fmap)(k:dim)(x z t:dart), inv_hmap m -> succ m k x -> let m0:= L (B m k x) k (top m k x) (bottom m k x) in eqc m0 z t <-> eqc m z t.
Proof.
simpl in |- *.
intros.
generalize (eqc_B m k x z t H H0).
simpl in |- *.
intro.
generalize (eqc_B_top m k x H H0).
intro.
assert (exd m x).
apply succ_exd with k.
tauto.
tauto.
generalize (eqc_B_bottom m k x H H3).
intro.
elim H1.
clear H1.
intros.
split.
clear H1.
intro.
elim H1.
tauto.
clear H1.
intro.
elim H1.
clear H1.
intro.
assert (eqc (B m k x) z (A m k x)).
apply eqc_trans with (top m k x).
tauto.
apply eqc_symm.
tauto.
assert (eqc (B m k x) x t).
apply eqc_trans with (bottom m k x).
tauto.
tauto.
tauto.
clear H1.
intro.
assert (eqc (B m k x) z x).
apply eqc_trans with (bottom m k x).
tauto.
apply eqc_symm.
tauto; tauto.
assert (eqc (B m k x) (A m k x) t).
apply eqc_trans with (top m k x).
tauto.
tauto.
tauto.
clear H5.
intro.
elim H1.
clear H1.
intro.
tauto.
clear H1.
intro.
elim H1.
clear H1.
intro.
right.
right.
split.
apply eqc_trans with x.
tauto.
tauto.
apply eqc_trans with (A m k x).
apply eqc_symm.
tauto.
tauto.
clear H1.
intro.
right.
left.
split.
apply eqc_trans with (A m k x).
tauto.
tauto.
apply eqc_trans with x.
apply eqc_symm.
tauto.
tauto.
Admitted.

Lemma MA0_f_cA0:forall(m:fmap)(z:dart), MA0.f m z = cA m zero z.
Proof.
Admitted.

Lemma Iter_cA0_L_B: forall(m:fmap)(k:dim)(x z:dart)(i:nat), inv_hmap m -> succ m k x -> let m0:= L (B m k x) k (top m k x) (bottom m k x) in Iter (MA0.f m0) i z = Iter (MA0.f m) i z.
Proof.
intros.
induction i.
simpl in |- *.
tauto.
simpl in |- *.
rewrite IHi in |- *.
rewrite MA0_f_cA0 in |- *.
rewrite MA0_f_cA0 in |- *.
unfold m0 in |- *.
induction k.
rewrite cA_L_B_top_bot in |- *.
tauto.
tauto.
tauto.
assert (zero = dim_opp one).
simpl in |- *.
tauto.
rewrite H1 in |- *.
apply cA_L_B_top_bot_ter.
tauto.
Admitted.

Lemma expe_L_B_top_bot:forall (m:fmap)(x z t:dart), inv_hmap m -> succ m zero x -> let m0:= L (B m zero x) zero (top m zero x) (bottom m zero x) in expe m0 z t <-> expe m z t.
Proof.
intros.
unfold expe in |- *.
split.
intro.
assert (inv_hmap m0).
unfold m0 in |- *.
apply inv_hmap_L_B_top_bot.
tauto.
tauto.
assert (exd m0 t).
apply MA0.expo_exd with z.
tauto.
tauto.
assert (exd m t).
generalize (exd_L_B_top_bot m zero x t).
unfold m0 in H2.
tauto.
assert (exd m0 z).
unfold MA0.expo in H1.
tauto.
generalize H1.
clear H1.
unfold MA0.expo in |- *.
assert (exd m z).
generalize (exd_L_B_top_bot m zero x z).
unfold m0 in H2.
tauto.
intro.
split.
tauto.
elim H6.
clear H6.
intros.
elim H7.
clear H7.
intros i Hi.
split with i.
generalize (Iter_cA0_L_B m zero x z i H H0).
simpl in |- *.
fold m0 in |- *.
intro.
rewrite <- H7 in |- *.
tauto.
intro.
assert (exd m z).
unfold MA0.expo in H1.
tauto.
assert (exd m0 z).
unfold m0 in |- *.
generalize (exd_L_B_top_bot m zero x z).
tauto.
unfold MA0.expo in H1.
elim H1.
clear H1.
intro.
intro.
elim H4.
intros i Hi.
clear H4.
unfold MA0.expo in |- *.
split.
tauto.
split with i.
unfold m0 in |- *.
rewrite <- Hi in |- *.
apply Iter_cA0_L_B.
tauto.
Admitted.

Lemma exd_Br1:forall(m:fmap)(x x' z:dart), exd m z <-> exd (Br1 m x x') z.
Proof.
unfold Br1 in |- *.
intros.
elim (succ_dec m zero x).
elim (succ_dec m zero x').
intros.
generalize (exd_B (L (B m zero x) zero (top m zero x) (bottom m zero x)) zero x' z).
simpl in |- *.
generalize (exd_B m zero x z).
tauto.
generalize (exd_B m zero x z).
tauto.
generalize (exd_B m zero x' z).
Admitted.

Lemma inv_hmap_Br1:forall(m:fmap)(x x':dart), inv_hmap m -> inv_hmap (Br1 m x x').
Proof.
unfold Br1 in |- *.
intros.
elim (succ_dec m zero x).
intro.
elim (succ_dec m zero x').
intros.
apply inv_hmap_B.
apply inv_hmap_L_B_top_bot.
tauto.
tauto.
intro.
apply inv_hmap_B.
tauto.
intro.
elim (succ_dec m zero x').
intro.
apply inv_hmap_B.
tauto.
intro.
rewrite not_succ_B in |- *.
tauto.
tauto.
Admitted.

Lemma planar_Br1:forall(m:fmap)(x x':dart), inv_hmap m -> planar m -> x <> x' -> planar (Br1 m x x').
Proof.
intros.
unfold Br1 in |- *.
elim (succ_dec m zero x).
elim (succ_dec m zero x').
intros.
apply planar_B0.
apply inv_hmap_L_B_top_bot.
tauto.
tauto.
unfold succ in |- *.
simpl in |- *.
elim (eq_dart_dec (top m zero x) x').
intro.
rewrite <- a1 in a.
absurd (succ m zero (top m zero x)).
apply not_succ_top.
tauto.
tauto.
intro.
rewrite A_B_bis in |- *.
unfold succ in a.
tauto.
intro.
symmetry in H2.
tauto.
apply planar_L_B_top_bot_0.
tauto.
tauto.
tauto.
intros.
apply planar_B0.
tauto.
tauto.
tauto.
intro.
elim (succ_dec m zero x').
intro.
apply planar_B0.
tauto.
tauto.
tauto.
intro.
rewrite not_succ_B in |- *.
tauto.
tauto.
Admitted.

Lemma double_link_comm: forall (m:fmap)(x x':dart), inv_hmap m -> double_link m x x' -> double_link m x' x.
Proof.
unfold double_link in |- *.
intros.
split.
intro.
symmetry in H1.
tauto.
unfold expe in |- *.
unfold expe in H.
apply MA0.expo_symm.
tauto.
Admitted.

Lemma double_link_succ :forall (m:fmap)(x x':dart), inv_hmap m -> double_link m x x' -> (succ m zero x \/ succ m zero x').
Proof.
intros.
unfold double_link in H0.
elim (succ_dec m zero x).
tauto.
elim (succ_dec m zero x').
tauto.
intros.
assert (exd m x).
unfold expe in H0.
unfold MA0.expo in H0.
tauto.
assert (exd m x').
unfold expe in H0.
apply MA0.expo_exd with x.
tauto.
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
elim H0.
intros.
elim H5.
rewrite <- H3 in |- *.
rewrite <- H4 in |- *.
apply expe_top.
tauto.
Admitted.

Lemma double_link_exd:forall(m:fmap)(x x':dart), inv_hmap m -> double_link m x x' -> exd m x /\ exd m x'.
Proof.
unfold double_link in |- *.
unfold expe in |- *.
intros.
generalize (MA0.expo_exd m x x').
intro.
unfold double_link in |- *.
unfold expe in |- *.
intros.
generalize (MA0.expo_exd m x x').
intro.
assert (exd m x).
unfold MA0.expo in H0.
tauto.
Admitted.

Lemma cA0_Br1:forall(m:fmap)(x x' z:dart), inv_hmap m -> double_link m x x' -> cA (Br1 m x x') zero z = if eq_dart_dec x z then cA m zero x' else if eq_dart_dec x' z then cA m zero x else cA m zero z.
Proof.
intros.
generalize (double_link_exd m x x' H H0).
intro Exx'.
unfold double_link in H0.
unfold expe in H0.
unfold Br1 in |- *.
set (m0 := L (B m zero x) zero (top m zero x) (bottom m zero x)) in |- *.
elim (succ_dec m zero x).
elim (succ_dec m zero x').
intros.
unfold m0 in |- *.
rewrite cA_B in |- *.
elim (eq_dart_dec x' z).
intro.
rewrite (bottom_L_B_top_bot m x x' H a0) in |- *.
elim (MA0.expo_dec m x x' H).
intro.
elim (eq_dart_dec x z).
intro.
rewrite <- a1 in a3.
rewrite cA_eq in |- *.
elim (succ_dec m zero x').
rewrite a3 in |- *.
tauto.
tauto.
tauto.
rewrite cA_eq in |- *.
elim (succ_dec m zero x).
tauto.
tauto.
tauto.
tauto.
tauto.
tauto.
elim (eq_dart_dec (top (L (B m zero x) zero (top m zero x) (bottom m zero x)) zero x') z).
intros.
rewrite (top_L_B_top_bot m x x' H) in a1.
generalize a1.
clear a1.
elim (MA0.expo_dec m x x').
intros.
rewrite A_L_B_top_bot in |- *.
elim (eq_dart_dec x x').
tauto.
elim (eq_dart_dec (top m zero x) x').
intros.
rewrite <- a3 in a.
absurd (succ m zero (top m zero x)).
apply not_succ_top.
tauto.
tauto.
elim (eq_dart_dec x z).
rewrite cA_eq in |- *.
elim (succ_dec m zero x').
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
rewrite (top_L_B_top_bot m x x' H) in |- *.
elim (MA0.expo_dec m x x' H).
intros.
rewrite cA_L_B_top_bot in |- *.
elim (eq_dart_dec x z).
tauto.
tauto.
tauto.
tauto.
tauto.
tauto.
tauto.
tauto.
apply inv_hmap_L_B_top_bot.
tauto.
tauto.
unfold succ in |- *.
simpl in |- *.
elim (eq_dart_dec (top m zero x) x').
intro.
rewrite <- a1 in a.
absurd (succ m zero (top m zero x)).
apply not_succ_top.
tauto.
tauto.
rewrite A_B_bis in |- *.
unfold succ in a.
tauto.
intro.
symmetry in H1.
tauto.
intros.
rewrite cA_B in |- *.
elim (eq_dart_dec x z).
intros.
rewrite cA_eq in |- *.
elim (succ_dec m zero x').
tauto.
intro.
apply expe_bottom.
tauto.
tauto.
tauto.
elim (eq_dart_dec (top m zero x) z).
elim (eq_dart_dec x' z).
rewrite cA_eq in |- *.
elim (succ_dec m zero x).
tauto.
tauto.
tauto.
intros.
rewrite cA_eq in |- *.
elim (succ_dec m zero z).
intro.
rewrite <- a0 in a1.
absurd (succ m zero (top m zero x)).
apply not_succ_top.
tauto.
tauto.
intros.
assert (top m zero x = top m zero x').
apply expe_top.
tauto.
tauto.
rewrite a0 in H1.
generalize (nosucc_top m zero x' H).
intro.
rewrite H2 in H1.
symmetry in H1.
tauto.
tauto.
tauto.
tauto.
elim (eq_dart_dec x' z).
intros.
rewrite <- a0 in b0.
generalize (expe_top m x x').
intros.
rewrite H1 in b0.
elim b0.
apply nosucc_top.
tauto.
tauto.
tauto.
tauto.
tauto.
tauto.
tauto.
tauto.
intro.
elim (eq_dart_dec x z).
rewrite cA_B in |- *.
elim (eq_dart_dec x' z).
intros.
rewrite <- a in a0.
tauto.
elim (eq_dart_dec (top m zero x') z).
intros.
rewrite cA_eq in |- *.
elim (succ_dec m zero x').
tauto.
intros.
assert (top m zero x = top m zero x').
apply (expe_top m x x').
tauto.
tauto.
generalize (nosucc_top m zero x').
intro.
rewrite H2 in a.
tauto.
tauto.
tauto.
tauto.
tauto.
intros.
assert (top m zero x = top m zero x').
apply expe_top.
tauto.
tauto.
rewrite <- H1 in b0.
generalize (nosucc_top m zero x).
intro.
rewrite H2 in b0.
tauto.
tauto.
tauto.
tauto.
tauto.
elim (succ_dec m zero x').
tauto.
intro.
assert (top m zero x = top m zero x').
apply expe_top.
tauto.
tauto.
generalize (nosucc_top m zero x).
generalize (nosucc_top m zero x').
intros.
rewrite H2 in H1.
rewrite H3 in H1.
tauto.
tauto.
tauto.
tauto.
tauto.
tauto.
tauto.
intro.
rewrite cA_B in |- *.
elim (eq_dart_dec x' z).
intros.
rewrite cA_eq in |- *.
elim (succ_dec m zero x).
tauto.
intro.
apply expe_bottom.
tauto.
apply MA0.expo_symm.
tauto.
tauto.
tauto.
elim (eq_dart_dec (top m zero x') z).
intros.
assert (top m zero x = top m zero x').
apply expe_top.
tauto.
tauto.
rewrite <- H1 in a.
generalize (nosucc_top m zero x).
intro.
rewrite H2 in a.
tauto.
tauto.
tauto.
tauto.
tauto.
tauto.
elim (succ_dec m zero x').
tauto.
intro.
assert (top m zero x = top m zero x').
apply expe_top.
tauto.
tauto.
generalize (nosucc_top m zero x).
generalize (nosucc_top m zero x').
intros.
rewrite H2 in H1.
rewrite H3 in H1.
tauto.
tauto.
tauto.
tauto.
tauto.
tauto.
Admitted.

Lemma cA0_1_Br1:forall(m:fmap)(x x' z:dart), inv_hmap m -> double_link m x x' -> cA_1 (Br1 m x x') zero z = if eq_dart_dec (cA m zero x) z then x' else if eq_dart_dec (cA m zero x') z then x else cA_1 m zero z.
Proof.
intros.
generalize (double_link_exd m x x' H H0).
intro Exx'.
elim (exd_dec m z).
intro.
set (t := cA_1 (Br1 m x x') zero z) in |- *.
assert (z = cA (Br1 m x x') zero t).
unfold t in |- *.
rewrite cA_cA_1 in |- *.
tauto.
apply inv_hmap_Br1.
tauto.
generalize (exd_Br1 m x x' z).
tauto.
generalize H1.
rewrite cA0_Br1 in |- *.
elim (eq_dart_dec x t).
intros.
elim (eq_dart_dec (cA m zero x) z).
intro.
unfold double_link in H0.
assert (x = cA_1 m zero z).
rewrite <- a1 in |- *.
rewrite cA_1_cA in |- *.
tauto.
tauto.
tauto.
rewrite H2 in H3.
rewrite cA_1_cA in H3.
tauto.
tauto.
tauto.
unfold double_link in |- *.
elim (eq_dart_dec (cA m zero x') z).
intros.
symmetry in |- *.
tauto.
symmetry in H2.
tauto.
elim (eq_dart_dec x' t).
intros.
elim (eq_dart_dec (cA m zero x) z).
symmetry in a0.
tauto.
symmetry in H2.
tauto.
elim (eq_dart_dec (cA m zero x) z).
intros.
assert (x = cA_1 m zero z).
rewrite <- a0 in |- *.
rewrite cA_1_cA in |- *.
tauto.
tauto.
unfold double_link in H0.
tauto.
rewrite H2 in H3.
rewrite cA_1_cA in H3.
tauto.
tauto.
apply cA_exd with zero.
tauto.
rewrite <- H2 in |- *.
apply exd_not_nil with m.
tauto.
tauto.
intros.
symmetry in H2.
elim (eq_dart_dec (cA m zero x') z).
intro.
assert (t = cA_1 m zero z).
rewrite <- H2 in |- *.
rewrite cA_1_cA in |- *.
tauto.
tauto.
apply cA_exd with zero.
tauto.
rewrite H2 in |- *.
apply exd_not_nil with m.
tauto.
tauto.
rewrite <- a0 in H3.
rewrite cA_1_cA in H3.
symmetry in H3.
tauto.
tauto.
unfold double_link in H0.
tauto.
intro.
rewrite <- H2 in |- *.
rewrite cA_1_cA in |- *.
tauto.
tauto.
apply cA_exd with zero.
tauto.
rewrite H2 in |- *.
apply exd_not_nil with m.
tauto.
tauto.
tauto.
tauto.
intro.
unfold double_link in H0.
assert (cA_1 (Br1 m x x') zero z = nil).
apply not_exd_cA_1.
apply inv_hmap_Br1.
tauto.
generalize (exd_Br1 m x x' z).
generalize (exd_dec m z).
generalize (exd_dec (Br1 m x x') z).
tauto.
elim (eq_dart_dec (cA m zero x) z).
intro.
rewrite <- a in b.
generalize (exd_cA_cA_1 m zero x).
tauto.
elim (eq_dart_dec (cA m zero x') z).
intros.
rewrite <- a in b.
generalize (exd_cA_cA_1 m zero x').
tauto.
intros.
rewrite H1 in |- *.
rewrite not_exd_cA_1 in |- *.
tauto.
tauto.
Admitted.

Lemma cA1_Br1:forall(m:fmap)(x x' z:dart), inv_hmap m -> cA (Br1 m x x') one z = cA m one z.
Proof.
unfold Br1 in |- *.
intros.
elim (succ_dec m zero x).
elim (succ_dec m zero x').
intros.
rewrite cA_B_ter in |- *.
simpl in |- *.
rewrite cA_B_ter in |- *.
tauto.
tauto.
intro.
inversion H0.
apply inv_hmap_L_B_top_bot.
tauto.
tauto.
intro.
inversion H0.
intros.
rewrite cA_B_ter in |- *.
tauto.
tauto.
intro.
inversion H0.
rewrite cA_B_ter in |- *.
tauto.
tauto.
intro.
Admitted.

Lemma cA1_1_Br1:forall(m:fmap)(x x' z:dart), inv_hmap m -> cA_1 (Br1 m x x') one z = cA_1 m one z.
Proof.
unfold Br1 in |- *.
intros.
elim (succ_dec m zero x).
elim (succ_dec m zero x').
intros.
rewrite cA_1_B_ter in |- *.
simpl in |- *.
rewrite cA_1_B_ter in |- *.
tauto.
tauto.
intro.
inversion H0.
apply inv_hmap_L_B_top_bot.
tauto.
tauto.
intro.
inversion H0.
intros.
rewrite cA_1_B_ter in |- *.
tauto.
tauto.
intro.
inversion H0.
rewrite cA_1_B_ter in |- *.
tauto.
tauto.
intro.
Admitted.

Lemma cF_Br1: forall(m:fmap)(x x' z:dart), inv_hmap m -> double_link m x x' -> cF (Br1 m x x') z = if eq_dart_dec (cA m zero x) z then cA_1 m one x' else if eq_dart_dec (cA m zero x') z then cA_1 m one x else cF m z.
Proof.
intros.
unfold cF in |- *.
rewrite cA1_1_Br1 in |- *.
rewrite cA0_1_Br1 in |- *.
elim (eq_dart_dec (cA m zero x) z).
intro.
tauto.
elim (eq_dart_dec (cA m zero x') z).
tauto.
tauto.
tauto.
tauto.
Admitted.

Lemma cF_1_Br1:forall(m:fmap)(x x' z:dart), inv_hmap m -> double_link m x x' -> cF_1 (Br1 m x x') z = if eq_dart_dec x (cA m one z) then cA m zero x' else if eq_dart_dec x' (cA m one z) then cA m zero x else cF_1 m z.
Proof.
intros.
unfold cF_1 in |- *.
rewrite cA1_Br1 in |- *.
rewrite cA0_Br1 in |- *.
tauto.
tauto.
tauto.
Admitted.

Lemma cF_1_Br1_bis:forall(m:fmap)(x x' z:dart), inv_hmap m -> double_link m x x' -> cF_1 (Br1 m x x') z = if eq_dart_dec (cA_1 m one x) z then cA m zero x' else if eq_dart_dec (cA_1 m one x') z then cA m zero x else cF_1 m z.
Proof.
intros.
unfold cF_1 in |- *.
rewrite cA1_Br1 in |- *.
rewrite cA0_Br1 in |- *.
generalize (double_link_exd m x x' H H0).
intro Exx'.
elim (exd_dec m z).
intro.
elim (eq_dart_dec x (cA m one z)).
elim (eq_dart_dec (cA_1 m one x) z).
tauto.
intros.
rewrite a0 in b.
rewrite cA_1_cA in b.
tauto.
tauto.
tauto.
elim (eq_dart_dec x' (cA m one z)).
elim (eq_dart_dec (cA_1 m one x) z).
intros.
rewrite <- a0 in b.
rewrite cA_cA_1 in b.
tauto.
tauto.
tauto.
elim (eq_dart_dec (cA_1 m one x') z).
tauto.
intros.
rewrite a0 in b.
rewrite cA_1_cA in b.
tauto.
tauto.
tauto.
elim (eq_dart_dec (cA_1 m one x) z).
intros.
rewrite <- a0 in b0.
rewrite cA_cA_1 in b0.
tauto.
tauto.
tauto.
elim (eq_dart_dec (cA_1 m one x') z).
intros.
rewrite <- a0 in b0.
rewrite cA_cA_1 in b0.
tauto.
tauto.
tauto.
tauto.
intro.
assert (cA m one z = nil).
apply not_exd_cA.
tauto.
tauto.
rewrite H1 in |- *.
elim (eq_dart_dec x nil).
intro.
rewrite a in Exx'.
absurd (exd m nil).
apply not_exd_nil.
tauto.
tauto.
elim (eq_dart_dec x' nil).
intro.
rewrite a in Exx'.
absurd (exd m nil).
apply not_exd_nil.
tauto.
tauto.
elim (eq_dart_dec (cA_1 m one x) z).
intros.
rewrite <- a in b.
absurd (exd m (cA_1 m one x)).
tauto.
generalize (exd_cA_1 m one x).
tauto.
elim (eq_dart_dec (cA_1 m one x') z).
intros.
rewrite <- a in b.
absurd (exd m (cA_1 m one x')).
tauto.
generalize (exd_cA_1 m one x').
tauto.
tauto.
tauto.
tauto.
Admitted.

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
Admitted.

Lemma Br1_comm: forall (m:fmap)(x x':dart), inv_hmap m -> double_link m x x' -> Br1 m x x' = Br1 m x' x.
Proof.
unfold double_link in |- *.
intros.
unfold Br1 in |- *.
elim (succ_dec m zero x).
elim (succ_dec m zero x').
simpl in |- *.
intros.
elim (eq_dart_dec (top m zero x) x').
intro.
rewrite <- a1 in a.
absurd (succ m zero (top m zero x)).
apply not_succ_top.
tauto.
tauto.
elim (eq_dart_dec (top m zero x') x).
intro.
rewrite <- a1 in a0; absurd (succ m zero (top m zero x')).
apply not_succ_top.
tauto.
tauto.
intros.
rewrite B_B in |- *.
assert (top m zero x = top m zero x').
apply expe_top.
tauto.
unfold expe in H0.
tauto.
assert (bottom m zero x = bottom m zero x').
apply expe_bottom.
tauto.
unfold expe in H0.
tauto.
rewrite <- H1 in |- *.
rewrite <- H2 in |- *.
tauto.
tauto.
intro.
elim (succ_dec m zero x').
tauto.
intro.
assert (top m zero x = x).
apply nosucc_top.
tauto.
unfold expe in |- *.
unfold expe in H0.
unfold MA0.expo in H0.
tauto.
tauto.
assert (top m zero x' = x').
apply nosucc_top.
tauto.
apply MA0.expo_exd with x.
tauto.
unfold expe in H0.
tauto.
tauto.
assert (top m zero x = top m zero x').
apply expe_top.
tauto.
unfold expe in H0.
tauto.
rewrite H1 in H3.
rewrite H2 in H3.
Admitted.

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
Admitted.

Lemma emptyl_dec:forall l:list, {emptyl l}+{~emptyl l}.
Proof.
induction l.
simpl in |- *.
tauto.
simpl in |- *.
Admitted.

Lemma isin1_dec:forall(l:list)(z:dart), {isin1 l z} + {~ isin1 l z}.
Proof.
induction l.
simpl in |- *.
tauto.
simpl in |- *.
intros.
intros.
generalize (IHl z).
generalize (eq_dart_dec d z).
Admitted.

Lemma isin2_dec:forall(l:list)(z:dart), {isin2 l z} + {~ isin2 l z}.
Proof.
induction l.
simpl in |- *.
tauto.
simpl in |- *.
intros.
intros.
generalize (IHl z).
generalize (eq_dart_dec d0 z).
Admitted.

Lemma exd_Br:forall(l:list)(m:fmap)(z:dart), exd m z <-> exd (Br m l) z.
Proof.
induction l.
simpl in |- *.
tauto.
simpl in |- *.
intro.
intro.
generalize (exd_Br1 m d d0 z).
generalize (IHl (Br1 m d d0) z).
Admitted.

Lemma inv_hmap_Br:forall(l:list)(m:fmap), inv_hmap m -> inv_hmap (Br m l).
Proof.
induction l.
simpl in |- *.
tauto.
intro.
simpl in |- *.
intro.
apply IHl.
apply inv_hmap_Br1.
Admitted.

Lemma not_succ_Br1_fst:forall(m:fmap)(x x':dart), inv_hmap m -> ~succ (Br1 m x x') zero x.
Proof.
unfold Br1.
intros.
elim (succ_dec m zero x).
elim (succ_dec m zero x').
intros.
unfold succ in |- *.
simpl in |- *.
elim (eq_dart_dec (top m zero x) x').
intro.
rewrite <- a1 in a.
absurd (succ m zero (top m zero x)).
apply not_succ_top.
tauto.
tauto.
simpl in |- *.
elim (eq_dart_dec (top m zero x) x).
intros.
rewrite <- a1 in a0.
absurd (succ m zero (top m zero x)).
apply not_succ_top.
tauto.
tauto.
intros.
elim (eq_dart_dec x x').
intro.
rewrite <- a1 in |- *.
rewrite A_B in |- *.
tauto.
apply inv_hmap_B.
tauto.
intro.
rewrite A_B_bis in |- *.
rewrite A_B in |- *.
tauto.
tauto.
tauto.
unfold succ in |- *.
rewrite A_B in |- *.
tauto.
tauto.
unfold succ in |- *.
elim (eq_dart_dec x x').
intros.
rewrite <- a in |- *.
rewrite A_B in |- *.
tauto.
tauto.
intros.
rewrite A_B_bis in |- *.
tauto.
Admitted.

Lemma not_succ_Br1_snd:forall(m:fmap)(x x':dart), inv_hmap m -> ~succ (Br1 m x x') zero x'.
Proof.
unfold Br1 in |- *.
intros.
elim (succ_dec m zero x).
elim (succ_dec m zero x').
intros.
unfold succ in |- *.
simpl in |- *.
elim (eq_dart_dec (top m zero x) x').
intro.
rewrite <- a1 in a.
absurd (succ m zero (top m zero x)).
apply not_succ_top.
tauto.
tauto.
intro.
simpl in |- *.
elim (eq_dart_dec (top m zero x) x').
tauto.
intro.
rewrite A_B in |- *.
tauto.
apply inv_hmap_B.
tauto.
unfold succ in |- *.
elim (eq_dart_dec x x').
intros.
rewrite <- a in |- *.
rewrite A_B in |- *.
tauto.
tauto.
intros.
rewrite A_B_bis in |- *.
tauto.
intro.
symmetry in H0.
tauto.
unfold succ in |- *.
rewrite A_B in |- *.
tauto.
Admitted.

Lemma cA1_Br:forall(l:list)(m:fmap)(z:dart), inv_hmap m -> cA (Br m l) one z = cA m one z.
Proof.
induction l.
simpl in |- *.
tauto.
simpl in |- *.
intros.
rewrite IHl in |- *.
rewrite cA1_Br1 in |- *.
tauto.
tauto.
apply inv_hmap_Br1.
Admitted.

Lemma cA1_1_Br:forall(l:list)(m:fmap)(z:dart), inv_hmap m -> cA_1 (Br m l) one z = cA_1 m one z.
Proof.
induction l.
simpl in |- *.
tauto.
simpl in |- *.
intros.
rewrite IHl in |- *.
rewrite cA1_1_Br1 in |- *.
tauto.
tauto.
apply inv_hmap_Br1.
Admitted.

Lemma Jordan1:forall(m:fmap)(x x':dart), inv_hmap m -> planar m -> let l:= cons x x' lam in ring m l -> nc (Br m l) = nc m + 1.
Proof.
unfold ring in |- *.
unfold pre_ring0 in |- *.
unfold pre_ring1 in |- *.
unfold pre_ring2 in |- *.
unfold pre_ring3 in |- *.
unfold double_link_list in |- *.
unfold double_link in |- *.
unfold distinct_face_list in |- *.
unfold distinct_edge_list in |- *.
unfold face_adjacent in |- *.
simpl in |- *.
intros.
decompose [and] H1.
clear H1 H2 H6 H5 H9 H3 H10 H12.
set (y := cA m zero x) in |- *.
set (y' := cA m zero x') in |- *.
fold y in H8.
fold y' in H8.
rewrite nc_Br1 in |- *.
fold y in |- *.
fold y' in |- *.
elim (expf_dec m y y').
tauto.
intro.
elim b.
apply expf_symm.
tauto.
tauto.
tauto.
unfold double_link in |- *.
Admitted.

Lemma expf_expf_B:forall (m:fmap)(x z t:dart), inv_hmap m -> succ m zero x -> let y := A m zero x in let x0 := bottom m zero x in ~expf m y x0 -> expf m z t -> expf (B m zero x) z t.
Proof.
intros.
generalize (expf_B0_CS m x z t H H0).
simpl in |- *.
fold x0 in |- *.
fold y in |- *.
assert (y = cA m zero x).
rewrite cA_eq in |- *.
elim (succ_dec m zero x).
unfold y in |- *.
tauto.
tauto.
tauto.
rewrite <- H3 in |- *.
elim (expf_dec m y x0).
tauto.
Admitted.

Lemma ring1_ring3_connect: forall(m:fmap)(x x' xs xs':dart)(l:list), let l1:= cons x x' (cons xs xs' l) in let y := cA m zero x in let y' := cA m zero x' in inv_hmap m -> planar m -> double_link_list m l1 -> pre_ring1 m l1 -> pre_ring3 m l1 -> ~ expf m y y'.
Proof.
simpl in |- *.
unfold double_link in |- *.
unfold distinct_faces in |- *.
unfold face_adjacent in |- *.
intros.
generalize H1 H2 H3.
clear H1 H2 H3.
set (y := cA m zero x) in |- *.
set (ys := cA m zero xs) in |- *.
set (y' := cA m zero x') in |- *.
set (xb0 := bottom m zero x) in |- *.
intros.
decompose [and] H1.
clear H1.
decompose [and] H2.
clear H2.
decompose [and] H3.
clear H3.
intro.
apply H13.
apply expf_trans with y'.
tauto.
Admitted.

Lemma expe_top_z:forall(m:fmap)(z:dart), inv_hmap m -> exd m z -> expe m z (top m zero z).
Proof.
intros.
generalize (expe_bottom_z m z H H0).
intro.
assert (top m zero (bottom m zero z) = top m zero z).
apply top_bottom_bis.
tauto.
tauto.
set (z0 := bottom m zero z) in |- *.
fold z0 in H1.
fold z0 in H2.
assert (cA_1 m zero z0 = top m zero z0).
rewrite cA_1_eq in |- *.
elim (pred_dec m zero z0).
unfold z0 in |- *.
intro.
absurd (pred m zero (bottom m zero z)).
apply not_pred_bottom.
tauto.
tauto.
tauto.
tauto.
unfold expe in |- *.
apply MA0.expo_trans with z0.
apply MA0.expo_symm.
tauto.
tauto.
rewrite <- H2 in |- *.
rewrite <- H3 in |- *.
apply MA0.expo_symm.
tauto.
unfold MA0.expo in |- *.
split.
assert (exd m z0).
unfold z0 in |- *.
apply exd_bottom.
tauto.
tauto.
generalize (exd_cA_1 m zero z0).
tauto.
split with 1%nat.
simpl in |- *.
rewrite <- cA0_MA0 in |- *.
rewrite cA_cA_1 in |- *.
tauto.
tauto.
unfold z0 in |- *.
Admitted.

Lemma expe_top_A:forall(m:fmap)(z:dart), inv_hmap m -> succ m zero z -> expe m (top m zero z) (A m zero z).
Proof.
intros.
assert (cA m zero z = A m zero z).
rewrite cA_eq in |- *.
elim (succ_dec m zero z).
tauto.
tauto.
tauto.
rewrite <- H1 in |- *.
assert (exd m z).
apply succ_exd with zero.
tauto.
tauto.
generalize (expe_top_z m z H H2).
unfold expe in |- *.
intro.
apply MA0.expo_trans with z.
apply MA0.expo_symm.
tauto.
tauto.
rewrite cA0_MA0 in |- *.
unfold MA0.expo in |- *.
split.
tauto.
split with 1%nat.
simpl in |- *.
Admitted.

Lemma expe_B_i: forall(m:fmap)(x z:dart)(i:nat), inv_hmap m -> succ m zero x -> exd m z -> let t := Iter (MA0.f (B m zero x)) i z in expe m z t.
Proof.
induction i.
simpl in |- *.
unfold expe in |- *.
intros.
apply MA0.expo_refl.
tauto.
simpl in |- *.
intros.
simpl in IHi.
set (t := Iter (MA0.f (B m zero x)) i z) in |- *.
fold t in IHi.
assert (MA0.f (B m zero x) t = cA (B m zero x) zero t).
tauto.
rewrite H2 in |- *.
rewrite cA_B in |- *.
elim (eq_dart_dec x t).
intro.
rewrite a in |- *.
unfold expe in |- *.
apply MA0.expo_trans with t.
tauto.
apply MA0.expo_symm.
tauto.
apply expe_bottom_z.
tauto.
assert (expe m z t).
tauto.
unfold expe in H3.
generalize (MA0.expo_exd m z t H H3).
tauto.
intro.
elim (eq_dart_dec (top m zero x) t).
intro.
assert (expe m z t).
tauto.
unfold expe in |- *.
apply MA0.expo_trans with t.
unfold expe in H3.
tauto.
rewrite <- a in |- *.
apply expe_top_A.
tauto.
tauto.
intro.
unfold expe in |- *.
apply MA0.expo_trans with t.
fold (expe m z t) in |- *.
tauto.
assert (cA m zero t = MA0.f m t).
tauto.
rewrite H3 in |- *.
unfold MA0.expo in |- *.
split.
generalize (exd_cA (B m zero x) zero t).
generalize (exd_B m zero x t).
generalize (inv_hmap_B m zero x).
generalize (MA0.exd_Iter_f (B m zero x) i z).
generalize (exd_B m zero x z).
tauto.
split with 1%nat.
simpl in |- *.
tauto.
tauto.
Admitted.

Lemma expe_B_expe: forall(m:fmap)(x z t:dart), inv_hmap m -> expe (B m zero x) z t -> expe m z t.
Proof.
intros.
assert (inv_hmap (B m zero x)).
apply inv_hmap_B.
tauto.
assert (MA0.expo (B m zero x) z t).
unfold expe in H0.
tauto.
assert (exd (B m zero x) t).
generalize (MA0.expo_exd (B m zero x) z t).
tauto.
assert (exd m t).
generalize (exd_B m zero x t).
tauto.
elim (succ_dec m zero x).
intro.
unfold MA0.expo in H2.
elim H2.
clear H2.
intros.
elim H5.
clear H5.
intros i Hi.
rewrite <- Hi in |- *.
apply expe_B_i.
tauto.
tauto.
generalize (exd_B m zero x z).
tauto.
intro.
generalize (not_succ_B m zero x).
intros.
rewrite H5 in H0.
tauto.
tauto.
Admitted.

Lemma expe_Br1_expe :forall(m:fmap)(x x' z t:dart), inv_hmap m -> expe (Br1 m x x') z t -> expe m z t.
Proof.
intros m x x' z t H.
unfold Br1 in |- *.
elim (succ_dec m zero x).
elim (succ_dec m zero x').
intros.
set (m0 := L (B m zero x) zero (top m zero x) (bottom m zero x)) in |- *.
fold m0 in H0.
assert (inv_hmap m0).
unfold m0 in |- *.
apply inv_hmap_L_B_top_bot.
tauto.
tauto.
generalize (expe_B_expe m0 x' z t H1 H0).
intro.
generalize (expe_L_B_top_bot m x z t H a0).
simpl in |- *.
fold m0 in |- *.
tauto.
intros.
apply expe_B_expe with x.
tauto.
tauto.
intro.
intro.
elim (succ_dec m zero x').
intro.
apply expe_B_expe with x'.
tauto.
tauto.
intro.
rewrite not_succ_B in H0.
tauto.
tauto.
Admitted.

Lemma distinct_edge_list_Br1: forall(m:fmap)(x x' xs xs':dart)(l:list), inv_hmap m -> planar m -> pre_ring0 m (cons x x' (cons xs xs' l)) -> distinct_edge_list (Br1 m x x') xs l.
Proof.
induction l.
simpl in |- *.
tauto.
simpl in |- *.
rename d into xss.
rename d0 into xss'.
intros.
simpl in |- *.
split.
apply IHl.
tauto.
tauto.
simpl in |- *.
tauto.
intro.
absurd (expe m xs xss).
tauto.
apply expe_Br1_expe with x x'.
tauto.
Admitted.

Lemma pre_ring0_Br1_aux: forall(m:fmap)(x x':dart)(l:list), inv_hmap m -> planar m -> pre_ring0 m (cons x x' l) -> pre_ring0 (Br1 m x x') l.
Proof.
induction l.
simpl in |- *.
tauto.
simpl in |- *.
rename d into xs.
rename d0 into xs'.
intros.
simpl in |- *.
split.
apply IHl.
tauto.
tauto.
simpl in |- *.
tauto.
apply distinct_edge_list_Br1 with xs'.
tauto.
tauto.
simpl in |- *.
Admitted.

Theorem disconnect_planar_criterion_Br1_bis: forall (m:fmap)(x x':dart), inv_hmap m -> planar m -> double_link m x x' -> let y := cA m zero x in let y' := cA m zero x' in (expf m y y' <-> ~eqc (Br1 m x x') x y).
Proof.
intros.
rewrite Br1_comm in |- *.
generalize (disconnect_planar_criterion_Br1 m x' x H H0).
generalize (double_link_comm m x x' H).
simpl in |- *.
fold y in |- *.
fold y' in |- *.
intros.
assert (expf m y' y <-> expf m y y').
split.
apply expf_symm.
apply expf_symm.
tauto.
tauto.
tauto.
