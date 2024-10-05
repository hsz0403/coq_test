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
tauto.
