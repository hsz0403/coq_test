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
