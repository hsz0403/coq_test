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
tauto.
