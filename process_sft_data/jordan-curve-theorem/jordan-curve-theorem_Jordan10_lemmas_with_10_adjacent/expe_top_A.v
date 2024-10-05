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
tauto.
