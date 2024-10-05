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

Lemma cA_L_B_top_bot:forall(m:fmap)(k:dim)(x z:dart), inv_hmap m -> succ m k x -> cA (L (B m k x) k (top m k x) (bottom m k x)) k z = cA m k z.
Proof.
induction k.
simpl in |- *.
intros.
elim (eq_dart_dec (top m zero x) z).
intro.
rewrite <- a in |- *.
rewrite cA_top in |- *.
tauto.
tauto.
apply succ_exd with zero.
tauto.
tauto.
elim (eq_dart_dec (cA_1 (B m zero x) zero (bottom m zero x)) z).
intros.
generalize a.
clear a.
rewrite cA_B in |- *.
rewrite cA_1_B in |- *.
elim (eq_dart_dec (A m zero x) (bottom m zero x)).
intro.
symmetry in a.
absurd (bottom m zero x = A m zero x).
apply succ_bottom.
tauto.
tauto.
tauto.
elim (eq_dart_dec (bottom m zero x) (bottom m zero x)).
elim (eq_dart_dec x (top m zero x)).
intros.
rewrite <- a in b.
tauto.
elim (eq_dart_dec (top m zero x) (top m zero x)).
rewrite cA_eq in |- *.
elim (succ_dec m zero z).
intros.
rewrite a2 in |- *.
tauto.
intros.
rewrite a1 in H0.
tauto.
tauto.
tauto.
tauto.
tauto.
tauto.
tauto.
tauto.
intros.
rewrite cA_B in |- *.
elim (eq_dart_dec x z).
intros.
rewrite cA_eq in |- *.
elim (succ_dec m zero z).
intro.
generalize b.
rewrite cA_1_B in |- *.
elim (eq_dart_dec (A m zero x) (bottom m zero x)).
intro.
symmetry in a1.
absurd (bottom m zero x = A m zero x).
apply succ_bottom.
tauto.
tauto.
tauto.
elim (eq_dart_dec (bottom m zero x) (bottom m zero x)).
intros.
tauto.
tauto.
tauto.
tauto.
rewrite a in |- *.
tauto.
tauto.
elim (eq_dart_dec (top m zero x) z).
tauto.
tauto.
tauto.
tauto.
intros.
assert (exd m x).
apply succ_exd with one.
tauto.
tauto.
simpl in |- *.
intros.
elim (eq_dart_dec (top m one x) z).
intro.
rewrite <- a in |- *.
rewrite cA_top in |- *.
tauto.
tauto.
tauto.
elim (eq_dart_dec (cA_1 (B m one x) one (bottom m one x)) z).
intros.
generalize a.
clear a.
rewrite cA_B in |- *.
rewrite cA_1_B in |- *.
elim (eq_dart_dec (A m one x) (bottom m one x)).
elim (eq_dart_dec x (top m one x)).
intros.
symmetry in a0.
absurd (bottom m one x = A m one x).
apply succ_bottom.
tauto.
tauto.
tauto.
elim (eq_dart_dec (top m one x) (top m one x)).
intros.
tauto.
intros.
rewrite a0 in |- *.
tauto.
elim (eq_dart_dec (bottom m one x) (bottom m one x)).
elim (eq_dart_dec x (top m one x)).
intros.
rewrite cA_eq in |- *.
elim (succ_dec m one z).
rewrite <- a1 in b.
symmetry in a.
tauto.
rewrite a1 in |- *.
tauto.
tauto.
elim (eq_dart_dec (top m one x) (top m one x)).
rewrite cA_eq in |- *.
intros.
elim (succ_dec m one z).
rewrite a1 in |- *.
tauto.
rewrite <- a1 in |- *.
tauto.
tauto.
tauto.
tauto.
tauto.
tauto.
tauto.
tauto.
rewrite cA_B in |- *.
rewrite cA_1_B in |- *.
elim (eq_dart_dec (A m one x) (bottom m one x)).
intro.
symmetry in a.
absurd (bottom m one x = A m one x).
apply succ_bottom.
tauto.
tauto.
tauto.
elim (eq_dart_dec (bottom m one x) (bottom m one x)).
elim (eq_dart_dec x z).
tauto.
elim (eq_dart_dec (top m one x) z).
rewrite cA_eq in |- *.
intros.
rewrite a in b2.
tauto.
tauto.
tauto.
tauto.
tauto.
tauto.
tauto.
tauto.
