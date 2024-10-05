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

Lemma pre_ring0_Br1: forall(m:fmap)(l:list), inv_hmap m -> planar m -> pre_ring0 m l -> let (x,x') := first l in pre_ring0 (Br1 m x x') (tail l).
Proof.
induction l.
simpl in |- *.
tauto.
intros.
simpl in |- *.
apply pre_ring0_Br1_aux.
tauto.
tauto.
Admitted.

Lemma expe_expe_B0: forall(m:fmap)(x z t:dart), inv_hmap m -> exd m x -> let m0 := B m zero x in ~ expe m x z -> expe m z t-> expe m0 z t.
Proof.
intros.
assert (exd m t).
apply MA0.expo_exd with z.
tauto.
unfold expe in H2.
tauto.
assert (exd m z).
unfold expe in H2.
unfold MA0.expo in H2.
tauto.
unfold m0 in |- *.
elim (succ_dec m zero x).
intro.
assert (bottom m zero z = bottom m zero t).
apply expe_bottom.
tauto.
unfold expe in H2.
tauto.
fold m0 in |- *.
assert (bottom m0 zero z = bottom m zero z).
unfold m0 in |- *.
apply not_expe_bottom_B0.
tauto.
tauto.
tauto.
tauto.
assert (~ expe m x t).
intro.
apply H1.
unfold expe in |- *.
apply MA0.expo_trans with t.
unfold expe in H7.
tauto.
apply MA0.expo_symm.
tauto.
unfold expe in H2.
tauto.
generalize (not_expe_bottom_B0 m x t H H3 H0 H7).
fold m0 in |- *.
intro.
rewrite H5 in H6.
rewrite <- H8 in H6.
apply bottom_bottom_expe.
unfold m0 in |- *.
apply inv_hmap_B.
tauto.
unfold m0 in |- *.
generalize (exd_B m zero x z).
tauto.
unfold m0 in |- *.
generalize (exd_B m zero x t).
tauto.
tauto.
intro.
rewrite not_succ_B in |- *.
tauto.
tauto.
Admitted.

Lemma double_link_list_Br1_aux: forall(m:fmap)(x x':dart)(l:list), inv_hmap m -> double_link_list m (cons x x' l) -> pre_ring0 m (cons x x' l) -> double_link_list (Br1 m x x') l.
Proof.
induction l.
simpl in |- *.
tauto.
simpl in |- *.
intros.
rename d into xs.
rename d0 into xs'.
split.
unfold Br1 in |- *.
elim (succ_dec m zero x).
elim (succ_dec m zero x').
intros.
unfold double_link in |- *.
unfold double_link in H0.
split.
tauto.
set (m0 := L (B m zero x) zero (top m zero x) (bottom m zero x)) in |- *.
unfold m0 in |- *.
generalize (expe_L_B_top_bot m x xs xs' H a0).
intro.
simpl in H2.
fold m0 in H2.
fold m0 in |- *.
assert (~ expe m x' xs).
intro.
absurd (expe m x xs).
tauto.
unfold expe in |- *.
apply MA0.expo_trans with x'.
unfold expe in H0.
tauto.
unfold expe in H3.
tauto.
assert (~ expe m0 x' xs).
intro.
apply H3.
generalize (expe_L_B_top_bot m x x' xs H a0).
intro.
simpl in H5.
fold m0 in H5.
tauto.
assert (exd m0 x').
unfold m0 in |- *.
generalize (exd_L_B_top_bot m zero x x').
assert (exd m x').
apply succ_exd with zero.
tauto.
tauto.
tauto.
unfold m0 in |- *.
assert (inv_hmap m0).
unfold m0 in |- *.
apply inv_hmap_L_B_top_bot.
tauto.
tauto.
generalize (expe_expe_B0 m0 x' xs xs' H6 H5).
intro.
fold m0 in |- *.
apply H7.
tauto.
tauto.
intros.
unfold double_link in |- *.
split.
unfold double_link in H0.
tauto.
unfold double_link in H0.
assert (exd m x).
apply succ_exd with zero.
tauto.
tauto.
apply expe_expe_B0.
tauto.
tauto.
tauto.
tauto.
intro.
elim (succ_dec m zero x').
intro.
unfold double_link in H0.
assert (~ expe m x' xs).
intro.
absurd (expe m x xs).
tauto.
unfold expe in |- *.
apply MA0.expo_trans with x'.
unfold expe in H0.
tauto.
unfold expe in H2.
tauto.
unfold double_link in |- *.
split.
tauto.
apply expe_expe_B0.
tauto.
apply succ_exd with zero.
tauto.
tauto.
tauto.
tauto.
intro.
rewrite not_succ_B in |- *.
tauto.
tauto.
tauto.
apply IHl.
tauto.
simpl in |- *.
tauto.
simpl in |- *.
Admitted.

Lemma double_link_list_Br1: forall(m:fmap)(l:list), inv_hmap m -> double_link_list m l -> pre_ring0 m l -> let (x,x') := first l in double_link_list (Br1 m x x') (tail l).
Proof.
induction l.
simpl in |- *.
tauto.
intros.
simpl in |- *.
apply double_link_list_Br1_aux.
tauto.
tauto.
Admitted.

Lemma planar_Br:forall(l:list)(m:fmap), inv_hmap m -> planar m -> pre_ring0 m l -> double_link_list m l -> planar (Br m l).
Proof.
induction l.
simpl in |- *.
tauto.
simpl in |- *.
intros.
apply IHl.
apply inv_hmap_Br1.
tauto.
apply planar_Br1.
tauto.
tauto.
unfold double_link in H2.
tauto.
assert (l = tail (cons d d0 l)).
simpl in |- *.
tauto.
generalize (pre_ring0_Br1 m (cons d d0 l)).
simpl in |- *.
tauto.
apply double_link_list_Br1_aux.
tauto.
simpl in |- *.
tauto.
simpl in |- *.
Admitted.

Lemma expf_Br1:forall(m:fmap)(x x' z t:dart), inv_hmap m -> planar m -> double_link m x x' -> let y:= cA m zero x in let y':= cA m zero x' in ~expf m y y' -> (expf m z t -> expf (Br1 m x x') z t).
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
assert (planar m0).
unfold m0 in |- *.
apply planar_L_B_top_bot_0.
tauto.
tauto.
tauto.
assert (~ expf m0 y y').
intro.
elim H1.
generalize (expf_L_B_top_bot m zero x y y' H a0).
fold m0 in |- *.
tauto.
assert (y = A m zero x).
unfold y in |- *.
rewrite cA_eq in |- *.
elim (succ_dec m zero x).
tauto.
tauto.
tauto.
assert (~ expf m0 (A m0 zero x') (bottom m0 zero x')).
unfold double_link in H1.
assert (exd m x').
apply MA0.expo_exd with x.
tauto.
unfold expe in H1.
tauto.
elim H1.
clear H1.
intros.
unfold m0 in |- *.
rewrite (bottom_L_B_top_bot m x x' H a0 H8 H1) in |- *.
elim (MA0.expo_dec m x x' H).
intro.
rewrite (A_L_B_top_bot m zero x x' H a0) in |- *.
elim (eq_dart_dec x x').
tauto.
elim (eq_dart_dec (top m zero x) x').
intros.
rewrite <- a2 in a.
absurd (succ m zero (top m zero x)).
apply not_succ_top.
tauto.
tauto.
intros.
fold m0 in |- *.
intro.
apply H6.
unfold y in |- *.
unfold y' in |- *.
rewrite cA_eq in |- *.
elim (succ_dec m zero x).
intro.
rewrite cA_eq in |- *.
elim (succ_dec m zero x').
intro.
apply expf_symm.
tauto.
tauto.
tauto.
tauto.
tauto.
unfold expe in H9.
tauto.
apply expf_expf_B.
tauto.
unfold succ in |- *.
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
unfold succ in a.
tauto.
tauto.
tauto.
tauto.
unfold m0 in |- *.
generalize (expf_L_B_top_bot m zero x z t H a0).
tauto.
intros.
assert (bottom m zero x = bottom m zero x').
apply expe_bottom.
tauto.
unfold double_link in H1.
unfold expe in H1.
tauto.
assert (bottom m zero x' = y').
unfold y' in |- *.
rewrite cA_eq in |- *.
elim (succ_dec m zero x').
tauto.
tauto.
tauto.
rewrite <- H4 in H5.
rewrite <- H5 in H2.
apply expf_expf_B.
tauto.
tauto.
unfold y in H2.
rewrite cA_eq in H2.
generalize H2.
clear H2.
elim (succ_dec m zero x).
tauto.
tauto.
tauto.
tauto.
intro.
elim (succ_dec m zero x').
intro.
assert (bottom m zero x = bottom m zero x').
apply expe_bottom.
tauto.
unfold double_link in H1.
unfold expe in H1.
tauto.
assert (bottom m zero x = y).
unfold y in |- *.
rewrite cA_eq in |- *.
elim (succ_dec m zero x).
tauto.
tauto.
tauto.
rewrite H4 in H5.
rewrite <- H5 in H2.
assert (y' = A m zero x').
unfold y' in |- *.
rewrite cA_eq in |- *.
elim (succ_dec m zero x').
tauto.
tauto.
tauto.
rewrite H6 in H2.
assert (~ expf m (A m zero x') (bottom m zero x')).
intro.
apply H2.
apply expf_symm.
tauto.
apply expf_expf_B.
tauto.
tauto.
tauto.
tauto.
intro.
rewrite not_succ_B in |- *.
tauto.
tauto.
Admitted.

Lemma pre_ring1_Br1_aux: forall(m:fmap)(x x':dart)(l:list), inv_hmap m -> planar m -> let y:= cA m zero x in let y':= cA m zero x' in double_link_list m (cons x x' l) -> pre_ring0 m (cons x x' l) -> pre_ring1 m l -> ~expf m y y' -> pre_ring1 (Br1 m x x') l.
Proof.
induction l.
simpl in |- *.
tauto.
simpl in |- *.
rename d into xs.
rename d0 into xs'.
intros.
induction l.
tauto.
rename d into xs0.
rename d0 into xs'0.
clear IHl0.
split.
apply IHl.
tauto.
tauto.
simpl in |- *.
simpl in H1.
tauto.
simpl in |- *.
simpl in H2.
tauto.
tauto.
tauto.
unfold face_adjacent in |- *.
unfold face_adjacent in H3.
elim H3.
clear H3.
intros.
decompose [and] H1.
clear H1.
decompose [and] H2.
clear H2.
clear IHl.
unfold double_link in H6.
unfold double_link in H8.
unfold expe in H6.
unfold expe in H8.
simpl in H11.
unfold expe in H11.
simpl in H1.
unfold expe in H1.
unfold expe in H12.
assert (~ MA0.expo m x xs').
intro.
apply H12.
apply MA0.expo_trans with xs'.
tauto.
apply MA0.expo_symm.
tauto.
tauto.
assert (~ MA0.expo m x' xs').
intro.
apply H2.
apply MA0.expo_trans with x'.
tauto.
tauto.
assert (~ MA0.expo m x' xs0).
intro.
elim H1.
intros.
apply H15.
apply MA0.expo_trans with x'.
tauto.
tauto.
rewrite cA0_Br1 in |- *.
elim (eq_dart_dec x xs').
intro.
rewrite <- a in H2.
elim H2.
apply MA0.expo_refl.
unfold MA0.expo in H6.
tauto.
elim (eq_dart_dec x' xs').
intros.
rewrite <- a in H7.
assert (exd m x').
apply MA0.expo_exd with x.
tauto.
tauto.
elim H7.
apply MA0.expo_refl.
tauto.
intros.
rewrite cA0_Br1 in |- *.
elim (eq_dart_dec x xs0).
intro.
rewrite <- a in H1.
absurd (MA0.expo m x x).
tauto.
apply MA0.expo_refl.
unfold MA0.expo in H6.
tauto.
elim (eq_dart_dec x' xs0).
intros.
rewrite <- a in H13.
elim H13.
apply MA0.expo_refl.
apply MA0.expo_exd with x.
tauto.
unfold MA0.expo in H6.
unfold MA0.expo in |- *.
tauto.
intros.
apply expf_Br1.
tauto.
tauto.
unfold double_link in |- *.
unfold expe in |- *.
tauto.
tauto.
tauto.
tauto.
unfold double_link in |- *.
unfold expe in |- *.
tauto.
tauto.
unfold double_link in |- *.
unfold expe in |- *.
Admitted.

Lemma expf_Br1_link:forall (m : fmap) (x x': dart), inv_hmap m -> planar m -> double_link m x x' -> let y :=cA m zero x in let y':=cA m zero x' in ~expf m y y' -> expf (Br1 m x x') y y'.
Proof.
intros.
set (m1 := Br1 m x x') in |- *.
assert (cF m1 y = cA_1 m one x').
unfold m1 in |- *.
rewrite cF_Br1 in |- *.
elim (eq_dart_dec (cA m zero x) y).
tauto.
unfold y in |- *.
tauto.
tauto.
tauto.
assert (cA_1 m1 one x' = cA_1 m one x').
unfold m1 in |- *.
unfold Br1 in |- *.
elim (succ_dec m zero x).
elim (succ_dec m zero x').
intros.
rewrite cA_1_B_ter in |- *.
assert (one = dim_opp zero).
simpl in |- *.
tauto.
rewrite H4 in |- *.
apply cA_1_L_B_top_bot_ter.
tauto.
tauto.
apply inv_hmap_L_B_top_bot.
tauto.
tauto.
intro.
inversion H4.
intros.
rewrite cA_1_B_ter in |- *.
tauto.
tauto.
intro.
inversion H4.
intro.
rewrite cA_1_B_ter in |- *.
tauto.
tauto.
intro.
inversion H4.
assert (cF m y' = cA_1 m one x').
unfold cF in |- *.
unfold y' in |- *.
rewrite cA_1_cA in |- *.
tauto.
tauto.
generalize (double_link_exd m x x').
tauto.
assert (expf m y' (cA_1 m one x')).
rewrite <- H5 in |- *.
unfold expf in |- *.
split.
tauto.
unfold MF.expo in |- *.
split.
assert (exd m x').
generalize (double_link_exd m x x').
tauto.
unfold y' in |- *.
generalize (exd_cA m zero x').
tauto.
split with 1%nat.
simpl in |- *.
tauto.
assert (expf m1 y (cA_1 m one x')).
rewrite <- H3 in |- *.
unfold expf in |- *.
split.
unfold m1 in |- *.
apply inv_hmap_Br1.
tauto.
unfold MF.expo in |- *.
split.
unfold m1 in |- *.
generalize (exd_Br1 m x x' y).
assert (exd m y).
unfold y in |- *.
generalize (exd_cA m zero x).
assert (exd m x).
generalize (double_link_exd m x x').
tauto.
tauto.
tauto.
split with 1%nat.
simpl in |- *.
tauto.
unfold Br1 in |- *.
unfold m1 in |- *.
fold m1 in |- *.
assert (expf m1 y' (cA_1 m one x')).
unfold m1 in |- *.
apply expf_Br1.
tauto.
tauto.
tauto.
fold y in |- *.
fold y' in |- *.
tauto.
tauto.
apply expf_trans with (cA_1 m one x').
tauto.
apply expf_symm.
Admitted.

Lemma distinct_last_darts: forall(m:fmap)(l:list)(x x' xf xf':dart), inv_hmap m -> double_link_list m (cons x x' (cons xf xf' l)) -> pre_ring0 m (cons x x' (cons xf xf' l)) -> let (xl, xl') := last (cons xf xf' l) in (x <> xl' /\ x' <> xl').
Proof.
induction l.
simpl in |- *.
intros.
decompose [and] H1.
clear H1.
decompose [and] H0.
clear H0.
unfold double_link in H1.
unfold double_link in H7.
unfold expe in H1.
unfold expe in H7.
unfold expe in H6.
elim H1.
clear H1.
intro.
elim H7.
clear H7.
intros.
assert (~ MA0.expo m x xf').
intro.
apply H6.
apply MA0.expo_trans with xf'.
tauto.
apply MA0.expo_symm.
tauto.
tauto.
assert (~ MA0.expo m x' xf').
intro.
apply H6.
apply MA0.expo_trans with x'.
tauto.
apply MA0.expo_trans with xf'.
tauto.
apply MA0.expo_symm.
tauto.
tauto.
split.
intro.
rewrite <- H11 in H9.
apply H9.
apply MA0.expo_refl.
unfold MA0.expo in H7.
tauto.
intro.
rewrite <- H11 in H10.
apply H10.
apply MA0.expo_refl.
apply MA0.expo_exd with x.
tauto.
tauto.
intros.
induction l.
simpl in H0.
simpl in H1.
simpl in |- *.
rename d into xs.
rename d0 into xs'.
simpl in IHl.
apply (IHl x x' xs xs').
tauto.
tauto.
tauto.
simpl in IHl.
simpl in |- *.
apply (IHl x x' xf xf').
tauto.
simpl in H0.
tauto.
simpl in H1.
Admitted.

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
Admitted.

Lemma betweenf_expf1:forall(m:fmap)(z v t:dart), inv_hmap m -> exd m z -> betweenf m z v t -> (expf m v z /\ expf m v t).
Proof.
intros.
assert (expf m z v /\ expf m z t).
apply (betweenf_expf m z v t H H0 H1).
split.
apply expf_symm.
tauto.
apply expf_trans with z.
apply expf_symm.
tauto.
Admitted.

Lemma not_expf_B:forall (m:fmap)(x z t:dart), inv_hmap m -> planar m -> succ m zero x -> let y := A m zero x in let x0 := bottom m zero x in (~expf m y z /\ ~expf m x0 z \/ ~expf m y t /\ ~expf m x0 t) -> ~expf m z t -> ~expf (B m zero x) z t.
Proof.
simpl in |- *.
intros.
set (x0 := cA m zero x) in |- *.
set (xb0 := bottom m zero x) in |- *.
fold x0 in H2.
fold xb0 in H2.
assert (x0 = A m zero x).
unfold x0 in |- *.
rewrite cA_eq in |- *.
elim (succ_dec m zero x).
tauto.
tauto.
tauto.
intro NC.
assert (inv_hmap (B m zero x)).
apply inv_hmap_B.
tauto.
assert (exd (B m zero x) z).
unfold expf in NC.
unfold MF.expo in NC.
tauto.
assert (exd m z).
generalize (exd_B m zero x z).
tauto.
assert (exd m x).
apply succ_exd with zero.
tauto.
tauto.
assert (exd m (top m zero x)).
apply exd_top.
tauto.
tauto.
assert (exd m (cA_1 m one (top m zero x))).
generalize (exd_cA_1 m one (top m zero x)).
tauto.
assert (exd m (cA_1 m one x)).
generalize (exd_cA_1 m one x).
tauto.
rename H11 into Fa.
generalize (expf_B0_CNS m x z t H H1).
simpl in |- *.
fold x0 in |- *.
fold xb0 in |- *.
elim (expf_dec m x0 xb0).
intros.
assert (betweenf m (cA_1 m one x) z xb0 /\ betweenf m (cA_1 m one x) t xb0 \/ betweenf m (cA_1 m one (top m zero x)) z x0 /\ betweenf m (cA_1 m one (top m zero x)) t x0 \/ ~ expf m (cA_1 m one x) z /\ expf m z t).
tauto.
clear H11.
elim H12.
clear H12.
intro.
decompose [and] H11.
clear H11.
generalize (betweenf_expf1 m (cA_1 m one x) z xb0 H Fa H12).
intro.
generalize (betweenf_expf1 m (cA_1 m one x) t xb0 H Fa H13).
intro.
assert (expf m xb0 z).
apply expf_symm.
tauto.
assert (expf m xb0 t).
apply expf_symm.
tauto.
tauto.
clear H12.
intro.
elim H11.
clear H11.
intro.
decompose [and] H11.
clear H11.
generalize (betweenf_expf1 m (cA_1 m one (top m zero x)) z x0 H H10 H12).
intro.
generalize (betweenf_expf1 m (cA_1 m one (top m zero x)) t x0 H H10 H13).
intro.
rewrite <- H4 in H2.
assert (expf m x0 z).
apply expf_symm.
tauto.
assert (expf m x0 t).
apply expf_symm.
tauto.
tauto.
tauto.
intros.
rewrite <- H4 in H2.
Admitted.

Lemma not_expf_Br1:forall (m:fmap)(x x' z t:dart), inv_hmap m -> planar m -> double_link m x x' -> let y := cA m zero x in let y' := cA m zero x' in (~expf m y z /\ ~expf m y' z \/ ~expf m y t /\ ~expf m y' t) -> ~expf m z t -> ~expf (Br1 m x x') z t.
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
assert (planar m0).
unfold m0 in |- *.
apply planar_L_B_top_bot_0.
tauto.
tauto.
tauto.
assert (~ expf m0 z t).
intro.
apply H3.
generalize (expf_L_B_top_bot m zero x z t H a0).
fold m0 in |- *.
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
rewrite (bottom_L_B_top_bot m x x' H a0 H9 H8) in |- *.
elim (MA0.expo_dec m x x').
unfold y in |- *.
rewrite cA_eq in |- *.
elim (succ_dec m zero x).
tauto.
tauto.
tauto.
tauto.
assert (succ m0 zero x').
unfold succ in |- *.
rewrite <- H7 in |- *.
unfold y' in |- *.
rewrite cA_eq in |- *.
elim (succ_dec m zero x').
fold (succ m zero x') in |- *.
tauto.
tauto.
tauto.
elim H2.
clear H2.
intro.
decompose [and] H2.
clear H2.
assert (~ expf m0 y z).
intro.
apply H10.
generalize (expf_L_B_top_bot m zero x y z H a0).
fold m0 in |- *.
tauto.
assert (~ expf m0 y' z).
intro.
apply H11.
generalize (expf_L_B_top_bot m zero x y' z H a0).
fold m0 in |- *.
tauto.
apply not_expf_B.
tauto.
tauto.
tauto.
rewrite <- H7 in |- *.
rewrite <- H8 in |- *.
tauto.
tauto.
intro.
decompose [and] H10.
clear H2 H10.
assert (~ expf m0 y t).
intro.
apply H11.
generalize (expf_L_B_top_bot m zero x y t H a0).
fold m0 in |- *.
tauto.
assert (~ expf m0 y' t).
intro.
apply H12.
generalize (expf_L_B_top_bot m zero x y' t H a0).
fold m0 in |- *.
tauto.
apply not_expf_B.
tauto.
tauto.
tauto.
rewrite <- H7 in |- *.
rewrite <- H8 in |- *.
tauto.
tauto.
intros.
assert (y' = bottom m zero x).
unfold y' in |- *.
rewrite cA_eq in |- *.
elim (succ_dec m zero x').
tauto.
intro.
symmetry in |- *.
apply expe_bottom.
tauto.
unfold double_link in H1.
unfold expe in H1.
tauto.
tauto.
assert (y = A m zero x).
unfold y in |- *.
rewrite cA_eq in |- *.
elim (succ_dec m zero x).
tauto.
tauto.
tauto.
apply not_expf_B.
tauto.
tauto.
tauto.
rewrite <- H5 in |- *.
rewrite <- H4 in |- *.
tauto.
tauto.
intro.
elim (succ_dec m zero x').
intro.
assert (y = bottom m zero x').
unfold y in |- *.
rewrite cA_eq in |- *.
elim (succ_dec m zero x).
elim (succ_dec m zero x').
tauto.
intro.
tauto.
intro.
apply expe_bottom.
tauto.
unfold double_link in H1.
unfold expe in H1.
tauto.
tauto.
assert (y' = A m zero x').
unfold y' in |- *.
rewrite cA_eq in |- *.
elim (succ_dec m zero x').
tauto.
tauto.
tauto.
apply not_expf_B.
tauto.
tauto.
tauto.
rewrite <- H5 in |- *.
rewrite <- H4 in |- *.
tauto.
tauto.
intro.
rewrite not_succ_B in |- *.
tauto.
tauto.
Admitted.

Lemma distinct_face_list_Br1_aux: forall(m:fmap)(x x' xs xs':dart)(l:list), inv_hmap m -> planar m -> let l1 := cons x x' (cons xs xs' l) in double_link_list m l1 -> pre_ring0 m l1 -> face_adjacent m x x' xs xs' -> pre_ring3 m l1 -> distinct_face_list (Br1 m x x') xs xs' l.
Proof.
induction l.
simpl in |- *.
tauto.
rename d into xs0.
rename d0 into xs'0.
intros.
simpl in |- *.
split.
apply IHl.
tauto.
tauto.
unfold l1 in H1.
simpl in H1.
simpl in |- *.
tauto.
unfold l1 in H2.
simpl in H2.
simpl in |- *.
tauto.
tauto.
unfold l1 in H4.
simpl in H4.
simpl in |- *.
tauto.
unfold l1 in H4.
simpl in H4.
generalize H4.
clear H4.
unfold distinct_faces in |- *.
intros.
decompose [and] H4.
clear H4.
unfold l1 in H1.
simpl in H1.
decompose [and] H1.
clear H1.
unfold face_adjacent in H3.
unfold l1 in H2.
simpl in H2.
decompose [and] H2.
clear H2.
unfold double_link in H4.
unfold double_link in H13.
unfold double_link in H8.
unfold double_link in H15.
assert (~ MA0.expo m x' xs).
intro.
apply H20.
unfold expe in |- *.
apply MA0.expo_trans with x'.
unfold expe in H4.
tauto.
tauto.
assert (~ MA0.expo m x' xs0).
intro.
apply H21.
unfold expe in |- *.
apply MA0.expo_trans with x'.
unfold expe in H4.
tauto.
tauto.
assert (cA (Br1 m x x') zero xs = cA m zero xs).
rewrite cA0_Br1 in |- *.
elim (eq_dart_dec x xs).
intro.
rewrite <- a in H20.
elim H20.
unfold expe in |- *.
apply MA0.expo_refl.
unfold expe in H4.
unfold MA0.expo in H4.
tauto.
elim (eq_dart_dec x' xs).
intro.
rewrite <- a in H2.
elim H2.
apply MA0.expo_refl.
apply MA0.expo_exd with x.
tauto.
unfold expe in H4.
tauto.
tauto.
tauto.
unfold double_link in |- *.
tauto.
assert (cA (Br1 m x x') zero xs0 = cA m zero xs0).
rewrite cA0_Br1 in |- *.
elim (eq_dart_dec x xs0).
intro.
rewrite <- a in H21.
elim H21.
unfold expe in |- *.
apply MA0.expo_refl.
unfold expe in H4.
unfold MA0.expo in H4.
tauto.
elim (eq_dart_dec x' xs0).
intro.
rewrite <- a in H17.
elim H17.
apply MA0.expo_refl.
apply MA0.expo_exd with x.
tauto.
unfold expe in H4.
tauto.
tauto.
tauto.
unfold double_link in |- *.
tauto.
rewrite H22 in |- *.
rewrite H23 in |- *.
apply not_expf_Br1.
tauto.
tauto.
unfold double_link in |- *.
tauto.
assert (~ expf m (cA m zero x') (cA m zero xs0)).
intro.
elim H10.
apply expf_trans with (cA m zero x').
apply expf_symm.
tauto.
tauto.
tauto.
Admitted.

Lemma distinct_faces_Br1: forall(m:fmap)(x x' xs xs' z z' zs zs':dart)(l:list), inv_hmap m -> planar m -> let l1:= cons x x' (cons xs xs' (cons z z' (cons zs zs' l))) in double_link_list m l1 -> pre_ring0 m l1 -> pre_ring3 m l1 -> face_adjacent m x x' xs xs' -> distinct_faces (Br1 m x x') z z' zs zs'.
Proof.
simpl in |- *.
unfold distinct_faces in |- *.
unfold double_link in |- *.
unfold expe in |- *.
intros.
decompose [and] H1.
clear H1.
decompose [and] H2.
clear H2.
decompose [and] H3.
clear H3.
assert (x <> z).
intro.
rewrite <- H3 in H23.
elim H23.
apply MA0.expo_refl.
unfold MA0.expo in H8.
tauto.
assert (x' <> z).
assert (~ MA0.expo m x' z).
intro.
elim H23.
apply MA0.expo_trans with x'.
tauto.
tauto.
intro.
rewrite <- H35 in H5.
elim H5.
apply MA0.expo_refl.
apply MA0.expo_exd with x.
tauto.
tauto.
assert (x <> zs).
intro.
rewrite <- H35 in H24.
elim H24.
apply MA0.expo_refl.
unfold MA0.expo in H8.
tauto.
assert (x' <> zs).
assert (~ MA0.expo m x' zs).
intro.
apply H24.
apply MA0.expo_trans with x'.
tauto.
tauto.
intro.
rewrite <- H37 in H36.
elim H36.
apply MA0.expo_refl.
apply MA0.expo_exd with x.
tauto.
tauto.
assert (cA (Br1 m x x') zero z = cA m zero z).
rewrite cA0_Br1 in |- *.
elim (eq_dart_dec x z).
tauto.
elim (eq_dart_dec x' z).
tauto.
tauto.
tauto.
unfold double_link in |- *.
unfold expe in |- *.
tauto.
assert (cA (Br1 m x x') zero zs = cA m zero zs).
rewrite cA0_Br1 in |- *.
elim (eq_dart_dec x zs).
tauto.
elim (eq_dart_dec x' zs).
tauto.
tauto.
tauto.
unfold double_link in |- *.
unfold expe in |- *.
tauto.
rewrite H37 in |- *.
rewrite H38 in |- *.
unfold face_adjacent in H4.
apply not_expf_Br1.
tauto.
tauto.
unfold double_link in |- *.
tauto.
assert (~ expf m (cA m zero x') (cA m zero z)).
intro.
apply H30.
apply expf_trans with (cA m zero x').
apply expf_symm.
tauto.
tauto.
tauto.
Admitted.

Lemma distinct_face_list_Br1_aux_bis: forall(m:fmap)(x x' xs xs' xf xf':dart)(l:list), inv_hmap m -> planar m -> let l1 := cons x x' (cons xs xs' (cons xf xf' l)) in double_link_list m l1 -> pre_ring0 m l1 -> face_adjacent m x x' xs xs' -> pre_ring3 m l1 -> distinct_face_list (Br1 m x x') xf xf' l.
Proof.
induction l.
simpl in |- *.
tauto.
rename d into xf0.
rename d0 into xf'0.
intros.
simpl in |- *.
split.
apply IHl.
tauto.
tauto.
unfold l1 in H1.
simpl in H1.
simpl in |- *.
tauto.
unfold l1 in H2.
simpl in H2.
simpl in |- *.
tauto.
tauto.
unfold l1 in H4.
simpl in H4.
simpl in |- *.
tauto.
apply (distinct_faces_Br1 m x x' xs xs' xf xf' xf0 xf'0 l).
tauto.
tauto.
fold l1 in |- *.
tauto.
fold l1 in |- *.
tauto.
fold l1 in |- *.
tauto.
Admitted.

Lemma pre_ring3_Br1_aux: forall(m:fmap)(x x' xs xs':dart)(l:list), inv_hmap m -> planar m -> let l1 := cons x x' (cons xs xs' l) in double_link_list m l1 -> pre_ring0 m l1 -> face_adjacent m x x' xs xs' -> pre_ring3 m l1 -> pre_ring3 (Br1 m x x') (cons xs xs' l).
Proof.
induction l.
simpl in |- *.
tauto.
rename d into xf.
rename d0 into xf'.
intros.
simpl in |- *.
assert (pre_ring3 (Br1 m x x') (cons xs xs' l)).
apply IHl.
tauto.
tauto.
unfold l1 in H1.
simpl in H1.
simpl in |- *.
tauto.
unfold l1 in H2.
simpl in H2.
simpl in |- *.
tauto.
tauto.
unfold l1 in H4.
simpl in H4.
simpl in |- *.
tauto.
unfold l1 in H4.
simpl in H5.
split.
split.
tauto.
apply distinct_face_list_Br1_aux_bis with xs xs'.
tauto.
tauto.
fold l1 in |- *.
tauto.
fold l1 in |- *.
tauto.
tauto.
tauto.
split.
apply distinct_face_list_Br1_aux.
tauto.
tauto.
unfold l1 in H1.
simpl in H1.
simpl in |- *.
tauto.
simpl in |- *.
unfold l1 in H2.
simpl in H2.
tauto.
tauto.
simpl in |- *.
simpl in H4.
tauto.
assert (distinct_face_list (Br1 m x x') xs xs' (cons xf xf' l)).
apply (distinct_face_list_Br1_aux m x x' xs xs' (cons xf xf' l)).
tauto.
tauto.
fold l1 in |- *.
tauto.
fold l1 in |- *.
tauto.
tauto.
tauto.
simpl in H6.
Admitted.

Lemma pre_ring3_Br1_aux_bis: forall(m:fmap)(x x' xs xs':dart)(l:list), inv_hmap m -> planar m -> let l1 := cons x x' (cons xs xs' l) in double_link_list m l1 -> pre_ring0 m l1 -> pre_ring1 m l1 -> pre_ring3 m l1 -> pre_ring3 (Br1 m x x') (cons xs xs' l).
Proof.
intros.
apply (pre_ring3_Br1_aux m x x' xs xs').
tauto.
tauto.
fold l1 in |- *.
tauto.
unfold l1 in H2.
tauto.
unfold l1 in H3.
simpl in H3.
tauto.
fold l1 in |- *.
Admitted.

Lemma pre_ring3_Br1: forall(m:fmap)(l:list), inv_hmap m -> planar m -> let (x,x') := first l in double_link_list m l -> pre_ring0 m l -> pre_ring1 m l -> pre_ring3 m l -> pre_ring3 (Br1 m x x') (tail l).
Proof.
induction l.
simpl in |- *.
tauto.
simpl in |- *.
rename d into x.
rename d0 into x'.
intros.
induction l.
simpl in |- *.
tauto.
rename d into xs.
rename d0 into xs'.
apply (pre_ring3_Br1_aux_bis m x x' xs xs' l).
tauto.
tauto.
simpl in |- *.
simpl in H1.
tauto.
simpl in |- *.
simpl in H2.
tauto.
simpl in |- *.
simpl in H3.
tauto.
simpl in |- *.
simpl in H4.
Admitted.

Lemma ring_Br1_aux: forall(m:fmap)(l:list), inv_hmap m -> planar m -> let x:= fst (first l) in let x' := snd (first l) in let y := cA m zero x in let y' := cA m zero x' in let m1 := Br1 m x x' in ~expf m y y' -> ring m l -> (emptyl (tail l) \/ ring m1 (tail l)).
Proof.
unfold ring in |- *.
intros.
set (x := fst (first l)) in |- *.
set (y := snd (first l)) in |- *.
elim (emptyl_dec (tail l)).
tauto.
right.
split.
tauto.
split.
generalize (double_link_list_Br1 m l).
induction (first l).
simpl in x.
simpl in y.
fold x in |- *.
fold y in |- *.
tauto.
split.
generalize (pre_ring0_Br1 m l).
induction (first l).
simpl in x.
simpl in y.
fold x in |- *.
fold y in |- *.
tauto.
split.
generalize (pre_ring1_Br1 m l).
induction (first l).
simpl in x.
simpl in y.
fold x in |- *.
fold y in |- *.
simpl in |- *.
simpl in H1.
fold x in H1.
fold y in H1.
tauto.
split.
generalize (pre_ring2_Br1 m l).
induction (first l).
simpl in |- *.
simpl in H1.
simpl in x.
simpl in y.
fold x in |- *.
fold y in |- *.
fold x in H1.
fold y in H1.
tauto.
generalize (pre_ring3_Br1 m l).
induction (first l).
simpl in x.
simpl in y.
fold x in |- *.
fold y in |- *.
simpl in H1.
fold x in H1.
fold y in H1.
Admitted.

Lemma ring_Br1: forall(m:fmap)(l:list), inv_hmap m -> planar m -> let x:= fst (first l) in let x' := snd (first l) in let m1 := Br1 m x x' in ring m l -> (emptyl (tail l) \/ ring m1 (tail l)).
Proof.
intros.
unfold m1 in |- *.
unfold ring in H1.
induction l.
unfold ring in H1.
simpl in H1.
tauto.
simpl in |- *.
simpl in x.
simpl in x'.
fold x in H1.
fold x' in H1.
induction l.
simpl in |- *.
tauto.
rename d1 into xs.
rename d2 into xs'.
set (y := cA m zero x) in |- *.
set (y' := cA m zero x') in |- *.
assert (~ expf m y y').
unfold y in |- *.
unfold y' in |- *.
apply (ring1_ring3_connect m x x' xs xs' l).
tauto.
tauto.
tauto.
tauto.
tauto.
generalize (ring_Br1_aux m (cons x x' (cons xs xs' l))).
simpl in |- *.
fold y in |- *.
fold y' in |- *.
intros.
apply H3.
tauto.
tauto.
tauto.
unfold ring in |- *.
Admitted.

Theorem Jordan: forall(l:list)(m:fmap), inv_hmap m -> planar m -> ring m l -> nc (Br m l) = nc m + 1.
Proof.
induction l.
unfold ring in |- *.
simpl in |- *.
tauto.
rename d into x.
rename d0 into x'.
simpl in |- *.
intros.
induction l.
simpl in |- *.
generalize (Jordan1 m x x').
simpl in |- *.
tauto.
rename d into xs.
rename d0 into xs'.
set (y := cA m zero x) in |- *.
set (y' := cA m zero x') in |- *.
assert (~ expf m y y').
unfold y in |- *.
unfold y' in |- *.
unfold ring in H1.
apply (ring1_ring3_connect m x x' xs xs' l).
tauto.
tauto.
tauto.
tauto.
tauto.
rewrite IHl in |- *.
rewrite nc_Br1 in |- *.
fold y in |- *.
fold y' in |- *.
elim (expf_dec m y y').
tauto.
intro.
omega.
tauto.
tauto.
unfold ring in H1.
simpl in H1.
tauto.
apply inv_hmap_Br1.
tauto.
apply planar_Br1.
tauto.
tauto.
unfold ring in H1.
simpl in H1.
unfold double_link in H1.
tauto.
generalize (ring_Br1 m (cons x x' (cons xs xs' l)) H H0 H1).
simpl in |- *.
Admitted.

Lemma pre_ring1_Br1: forall(m:fmap)(l:list), inv_hmap m -> planar m -> double_link_list m l -> pre_ring0 m l -> pre_ring1 m l -> let (x,x') := first l in let y := cA m zero x in let y' := cA m zero x' in ~expf m y y' -> pre_ring1 (Br1 m x x') (tail l).
Proof.
induction l.
simpl in |- *.
tauto.
simpl in |- *.
rename d into x.
rename d0 into x'.
intros.
apply pre_ring1_Br1_aux.
tauto.
tauto.
simpl in |- *.
tauto.
simpl in |- *.
tauto.
generalize H3.
clear H3.
elim l.
simpl in |- *.
tauto.
intros.
tauto.
tauto.
