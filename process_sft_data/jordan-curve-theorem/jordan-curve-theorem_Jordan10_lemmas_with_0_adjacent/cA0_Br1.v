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
tauto.
