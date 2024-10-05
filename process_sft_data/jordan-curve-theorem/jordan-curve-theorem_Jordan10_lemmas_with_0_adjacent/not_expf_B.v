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
tauto.
