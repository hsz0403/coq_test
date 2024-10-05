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

Lemma bottom_L_B_top_bot: forall(m:fmap)(x z:dart)(H:inv_hmap m), succ m zero x -> exd m z -> x <> z -> let m0:= L (B m zero x) zero (top m zero x) (bottom m zero x) in bottom m0 zero z = if MA0.expo_dec m x z H then (A m zero x) else bottom m zero z.
Proof.
intros.
unfold m0 in |- *.
simpl in |- *.
assert (exd m x).
apply succ_exd with zero.
tauto.
tauto.
assert (exd m (top m zero x)).
apply exd_top.
tauto.
tauto.
assert (x <> top m zero x).
intro.
rewrite H5 in H0.
absurd (succ m zero (top m zero x)).
apply not_succ_top.
tauto.
tauto.
generalize (between_bottom_B0_bis m x (top m zero x) H H4 H3 H5).
simpl in |- *.
rewrite bottom_top_bis in |- *.
intros.
generalize (between_bottom_B0_bis m x z H H1 H3 H2).
simpl in |- *.
intros.
assert (exd m (bottom m zero x)).
apply exd_bottom.
tauto.
tauto.
generalize (betweene_dec1 m (bottom m zero x) x (top m zero x) H H8 H3).
assert (exd m (bottom m zero z)).
apply exd_bottom.
tauto.
tauto.
generalize (betweene_dec1 m (bottom m zero z) x z H H9 H3).
intro.
intro.
decompose [and] H6.
decompose [and] H7.
clear H6 H7.
generalize (not_expe_bottom_B0 m x z H H1 H3).
simpl in |- *.
unfold expe in |- *.
intro.
elim H10.
clear H10.
intro.
generalize (H14 H7).
intro.
clear H14.
rewrite H10 in |- *.
elim (eq_dart_dec (bottom m zero x) (A m zero x)).
intro.
absurd (bottom m zero x = A m zero x).
apply succ_bottom.
tauto.
tauto.
tauto.
intro.
elim (MA0.expo_dec m x z H).
tauto.
intro.
unfold betweene in H7.
generalize (MA0.between_expo m (bottom m zero z) x z).
intros.
elim b0.
apply MA0.expo_trans with (bottom m zero z).
apply MA0.expo_symm.
tauto.
tauto.
tauto.
intro.
generalize (H15 H7).
clear H15.
intro.
rewrite H15 in |- *.
elim (MA0.expo_dec m x z H).
intro.
elim (eq_dart_dec (bottom m zero x) (bottom m zero z)).
intros.
apply H12.
unfold betweene in |- *.
apply betweene_bottom_x_top.
tauto.
tauto.
intro.
elim b.
apply expe_bottom.
tauto.
tauto.
elim (eq_dart_dec (bottom m zero x) (bottom m zero z)).
intros.
elim b.
clear b.
apply MA0.expo_trans with (bottom m zero x).
apply MA0.expo_symm.
tauto.
apply expe_bottom_z.
tauto.
tauto.
rewrite a in |- *.
apply expe_bottom_z.
tauto.
tauto.
tauto.
tauto.
tauto.
