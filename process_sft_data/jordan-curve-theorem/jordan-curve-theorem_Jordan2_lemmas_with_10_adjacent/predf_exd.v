Require Export Jordan1.
Require Euclid.
Require Compare.
Require Recdef.
Require Arith.
Inductive set:Set:= Vs : set | Is : set -> dart -> set.
Fixpoint exds(s:set)(z:dart){struct s}:Prop:= match s with Vs => False | Is s0 x => x=z \/ exds s0 z end.
Fixpoint Ds(s:set)(z:dart){struct s}:set:= match s with Vs => Vs | Is s0 x => if eq_dart_dec x z then (Ds s0 z) else Is (Ds s0 z) x end.
Fixpoint card(s:set):nat:= match s with Vs => 0%nat | Is s0 x => if exds_dec s0 x then card s0 else (1 + card s0)%nat end.
Fixpoint fmap_to_set(m:fmap):set:= match m with V => Vs | I m0 x _ _ => Is (fmap_to_set m0) x | L m0 _ _ _ => (fmap_to_set m0) end.
Fixpoint ndN (m:fmap):nat:= match m with V => 0%nat | I m0 x _ _ => if exd_dec m0 x then ndN m0 else (1 + ndN m0)%nat | L m0 _ _ _ => ndN m0 end.
Fixpoint set_minus(s1 s2:set){struct s1}:set:= match s1 with Vs => Vs | Is s0 x => if exds_dec s2 x then set_minus s0 s2 else Is (set_minus s0 s2) x end.
Inductive incls(s1 s2:set):Prop:= exds2 : (forall z:dart, exds s1 z -> exds s2 z) -> incls s1 s2.
Definition impls(s1 s2:set):Prop:= forall z:dart, exds s1 z -> exds s2 z.
Definition eqs(s1 s2:set):Prop:= forall z:dart, exds s1 z <-> exds s2 z.
Definition disjs(s1 s2:set):Prop:= forall z:dart, exds s1 z -> exds s2 z -> False.
Definition Rs(sy sx:set):= (card sy < card sx)%nat.
Fixpoint Iter(g:dart->dart)(n:nat)(z:dart){struct n}:dart:= match n with 0%nat => z | S n0 => g (Iter g n0 z) end.
Module Type Sigf.
Parameter f : fmap -> dart -> dart.
Parameter f_1 : fmap -> dart -> dart.
Axiom exd_f:forall (m:fmap)(z:dart), inv_hmap m -> (exd m z <-> exd m (f m z)).
Axiom bij_f : forall m:fmap, inv_hmap m -> bij_dart (exd m) (f m).
Axiom exd_f_1:forall (m:fmap)(z:dart), inv_hmap m -> (exd m z <-> exd m (f_1 m z)).
Axiom bij_f_1 : forall m:fmap, inv_hmap m -> bij_dart (exd m) (f_1 m).
Axiom f_1_f : forall (m:fmap)(z:dart), inv_hmap m -> exd m z -> f_1 m (f m z) = z.
Axiom f_f_1 : forall (m:fmap )(z:dart), inv_hmap m -> exd m z -> f m (f_1 m z) = z.
End Sigf.
Module Mf(M:Sigf)<:Sigf with Definition f:=M.f with Definition f_1:=M.f_1.
Definition f:=M.f.
Definition f_1:=M.f_1.
Definition exd_f:=M.exd_f.
Definition exd_f_1:=M.exd_f_1.
Definition bij_f:=M.bij_f.
Definition bij_f_1:=M.bij_f_1.
Definition f_1_f:=M.f_1_f.
Definition f_f_1:=M.f_f_1.
Definition P1 (m:fmap)(z:dart)(s:set):Prop:= let sr := Iter_rem_aux m z s in let n := Iter_upb_aux m z s in ~ exds sr (Iter (f m) n z).
Definition R3 (m:fmap)(z t:dart)(s:set):Prop:= ~ exds s t -> let sr := Iter_rem_aux m z s in ~ exds sr t.
Definition R2 (m:fmap)(z:dart)(s:set):Prop:= let sr := Iter_rem_aux m z s in ~ exds sr (Iter (f m) (ndN m - card s)%nat z).
Definition R1 (m:fmap)(z:dart)(i:nat)(s:set):Prop:= let sr := Iter_rem_aux m z s in let n := Iter_upb_aux m z s in (ndN m - card s <= i <= n)%nat -> ~ exds sr (Iter (f m) i z).
Definition P2 (m:fmap)(z:dart)(s:set):Prop:= (card s < ndN m -> card (Iter_rem_aux m z s) < ndN m)%nat.
Definition P2_bis (m:fmap)(z:dart)(s:set):Prop:= (card s <= ndN m -> card (Iter_rem_aux m z s) <= ndN m)%nat.
Definition Q1(m:fmap)(z:dart)(s:set):Prop:= (card (Iter_rem_aux m z s) <= card s)%nat.
Definition Q2(m:fmap)(z:dart)(s:set):Prop:= exds s (Iter (f m) (ndN m - card s)%nat z) -> (card (Iter_rem_aux m z s) < card s)%nat.
Definition PL2(m:fmap)(z t:dart)(x:set):Prop:= inv_hmap m -> exd m z -> exds x t -> let sr:= Iter_rem_aux m z x in let zn0 := (Iter (f m) (ndN m - card x)%nat z) in ~exds sr t -> exds x zn0 -> ~ exds (Iter_rem_aux m z (Ds x zn0)) t.
Definition PL3(m:fmap)(z t:dart)(x:set):Prop:= inv_hmap m -> exd m z -> exds x t -> let sr:= Iter_rem_aux m z x in let zn0 := (Iter (f m) (ndN m - card x)%nat z) in ~exds sr t -> exds x zn0.
Definition P4(m:fmap)(z t:dart)(s:set):Set:= inv_hmap m -> exd m z -> exds s t -> (card s <= ndN m)%nat -> let sr:= Iter_rem_aux m z s in let nr:= Iter_upb_aux m z s in ~ exds sr t -> {i:nat | (i < nr)%nat /\ Iter (f m) i z = t}.
Definition diff_int_aux (m:fmap)(z:dart)(a b:nat)(t:dart): Prop:= forall i : nat, (a <= i <= b)%nat -> Iter (f m) i z <> t.
Definition diff_int (m:fmap)(z:dart)(a b:nat): Prop:= forall i j : nat, (a <= i /\ i < j /\ j <= b)%nat -> Iter (f m) i z <> Iter (f m) j z.
Definition exds_int(m:fmap)(z:dart)(a b:nat)(s:set):Prop:= forall i:nat, (a <= i <= b)%nat -> exds s (Iter (f m) i z).
Definition P6(m:fmap)(z:dart)(s:set):Prop:= inv_hmap m -> (card s <= ndN m -> let n0:= ndN m - card s in let nr:= Iter_upb_aux m z s in exds s (Iter (f m) n0 z) -> exds_int m z n0 (nr - 1) s)%nat.
Definition P7(m:fmap)(z:dart)(s:set):Prop:= inv_hmap m -> (card s <= ndN m -> let n0:= ndN m - card s in let nr:= Iter_upb_aux m z s in exds s (Iter (f m) n0 z) -> forall j:nat, n0 < j <= nr - 1 -> Iter (f m) n0 z <> Iter (f m) j z)%nat.
Definition P8(m:fmap)(z:dart)(s:set):Prop:= inv_hmap m -> (card s <= ndN m -> let n0:= ndN m - card s in let nr:= Iter_upb_aux m z s in exds s (Iter (f m) n0 z) -> diff_int m z n0 (nr - 1))%nat.
Definition diff_orb(m:fmap)(z:dart):Prop:= let nr:= Iter_upb_aux m z (fmap_to_set m) in (diff_int m z 0 (nr - 1))%nat.
Import Euclid.
Export Compare.
Definition expo(m:fmap)(z t:dart):Prop:= exd m z /\ exists i:nat, Iter (f m) i z = t.
Definition expo1 (m:fmap)(z t:dart):Prop:= exd m z /\ let p:= Iter_upb m z in exists j:nat, (j < p)%nat /\ Iter (f m) j z = t.
Definition modulo(m:fmap)(z:dart)(i:dart) (hi:inv_hmap m)(he:exd m z):nat.
Proof.
intros.
assert (let p := Iter_upb m z in {j : nat | Iter (f m) i z = Iter (f m) j z /\ (j < p)%nat}).
apply mod_p.
tauto.
tauto.
simpl in H.
elim H.
intros.
apply x.
Defined.
Fixpoint ex_j (m:fmap)(z t:dart)(n:nat){struct n}:Prop:= match n with 0%nat => z = t | S n0 => Iter (f m) n z = t \/ ex_j m z t n0 end.
Open Scope nat_scope.
Import Recdef.
Open Scope nat_scope.
Function degree_aux(m:fmap)(z:dart)(n:nat) {measure (fun i:nat => ndN m - i) n}:nat:= if le_lt_dec n (ndN m) then if eq_dart_dec z (Iter (f m) n z) then n else if eq_nat_dec n (ndN m) then (ndN m) + 1 else degree_aux m z (n+1) else (ndN m) + 1.
Proof.
intros.
omega.
Defined.
Definition degree(m:fmap)(z:dart):= degree_aux m z 1.
Definition P_degree_pos(m:fmap)(z:dart)(n1 n2:nat): Prop:= exd m z -> 0 < n1 -> 0 < n2.
Definition P_degree_diff(m:fmap)(z:dart)(n1 n2:nat): Prop:= inv_hmap m -> exd m z -> 0 < n1 -> forall i:nat, n1 <= i < n2 -> Iter (f m) i z <> z.
Definition P_degree_per(m:fmap)(z:dart)(n1 n2:nat): Prop:= inv_hmap m -> exd m z -> 0 < n1 -> n2 <= ndN m -> Iter (f m) n2 z = z.
Import Arith.
Open Scope R_scope.
Open Scope nat_scope.
Open Scope nat_scope.
Open Scope R_scope.
Definition between(m:fmap)(z v t:dart):Prop:= inv_hmap m -> exd m z -> exists i:nat, exists j:nat, Iter (f m) i z = v /\ Iter (f m) j z = t /\ (i <= j < Iter_upb m z)%nat.
End Mf.
Module Type Sigd.
Parameter k:dim.
End Sigd.
Module McA(Md:Sigd)<:Sigf.
Definition f := fun(m:fmap)(z:dart) => cA m Md.k z.
Definition f_1 := fun(m:fmap)(z:dart) => cA_1 m Md.k z.
Definition exd_f := fun(m:fmap)(z:dart) => exd_cA m Md.k z.
Definition exd_f_1 := fun(m:fmap)(z:dart) => exd_cA_1 m Md.k z.
Definition bij_f := fun(m:fmap)(h:inv_hmap m) => bij_cA m Md.k h.
Definition bij_f_1 := fun(m:fmap)(h:inv_hmap m) => bij_cA_1 m Md.k h.
Definition f_1_f := fun(m:fmap)(z:dart) => cA_1_cA m Md.k z.
Definition f_f_1 := fun(m:fmap)(z:dart) => cA_cA_1 m Md.k z.
End McA.
Module Md0<:Sigd.
Definition k:=zero.
End Md0.
Module Md1<:Sigd.
Definition k:=one.
End Md1.
Module McA0:=McA Md0.
Module MA0:= Mf McA0.
Module McA1:=McA Md1.
Module MA1:= Mf McA1.
Definition F(m:fmap)(z:dart):= A_1 m one (A_1 m zero z).
Definition succf(m:fmap)(z:dart):Prop:= pred m zero z /\ pred m one (A_1 m zero z).
Definition F_1 (m:fmap)(z:dart):= A m zero (A m one z).
Definition predf(m:fmap)(z:dart):Prop:= succ m one z /\ succ m zero (A m one z).
Definition cF (m:fmap)(z:dart):= cA_1 m one (cA_1 m zero z).
Definition cF_1 (m:fmap)(z:dart):= cA m zero (cA m one z).
Module McF<:Sigf.
Definition f := cF.
Definition f_1 := cF_1.
Definition exd_f := exd_cF.
Definition exd_f_1 := exd_cF_1.
Definition bij_f := bij_cF.
Definition bij_f_1 := bij_cF_1.
Definition f_1_f := cF_1_cF.
Definition f_f_1 := cF_cF_1.
End McF.
Module MF:= Mf McF.

Theorem degree_sum_bound: forall(m:fmap)(x y:dart), inv_hmap m -> exd m x -> exd m y -> ~expo m x y -> degree m x + degree m y <= ndN m.
Proof.
intros.
rewrite <- upb_eq_degree in |- *.
rewrite <- upb_eq_degree in |- *.
apply (upb_sum_bound m x y H H0 H1 H2).
tauto.
tauto.
tauto.
Admitted.

Lemma between_expo1:forall(m:fmap)(z v t:dart), inv_hmap m -> exd m z -> between m z v t -> expo1 m z v /\ expo1 m z t.
Proof.
unfold between in |- *.
intros.
generalize (H1 H H0).
clear H1.
intro.
elim H1.
intros i Hi.
clear H1.
elim Hi.
clear Hi.
intros j Hj.
decompose [and] Hj.
clear Hj.
unfold expo1 in |- *.
split.
split.
tauto.
split with i.
split.
omega.
tauto.
split.
tauto.
split with j.
split.
tauto.
Admitted.

Lemma between_expo:forall(m:fmap)(z v t:dart), inv_hmap m -> exd m z -> between m z v t -> expo m z v /\ expo m z t.
Proof.
intros.
generalize (between_expo1 m z v t H H0 H1).
intros.
generalize (expo_expo1 m z v H).
generalize (expo_expo1 m z t H).
Admitted.

Lemma between_expo_refl_1:forall(m:fmap)(z t:dart), inv_hmap m -> exd m z -> (between m z z t <-> expo1 m z t).
Proof.
intros.
unfold between in |- *.
unfold expo1 in |- *.
split.
intros.
generalize (H1 H H0).
clear H1.
intro.
elim H1.
clear H1.
intros i Hi.
elim Hi.
intros j Hj.
split.
tauto.
split with j.
tauto.
intros.
intuition.
elim H5.
intros i Hi.
clear H5.
split with 0%nat.
split with i.
simpl in |- *.
split.
tauto.
split.
tauto.
Admitted.

Lemma between_expo_refl_2:forall(m:fmap)(z t:dart), inv_hmap m -> exd m z -> (between m z t t <-> expo1 m z t).
Proof.
intros.
unfold between in |- *.
unfold expo1 in |- *.
split.
intros.
generalize (H1 H H0).
clear H1.
intro.
intuition.
elim H1.
clear H1.
intros i Hi.
elim Hi.
intros j Hj.
split with j.
tauto.
intros.
decompose [and] H1.
clear H1.
elim H5.
clear H5.
intros j Hj.
split with j.
split with j.
split.
tauto.
split.
tauto.
split.
omega.
Admitted.

Lemma expo_between_1:forall(m:fmap)(z t:dart), inv_hmap m -> exd m z -> (expo1 m z t <-> between m z t (f_1 m z)).
Proof.
intros.
rename H0 into Ez.
unfold between in |- *.
unfold expo1 in |- *.
split.
intros.
intuition.
elim H4.
intros j Hj.
clear H4.
split with j.
split with (Iter_upb m z - 1)%nat.
split.
tauto.
split.
set (nr := Iter_upb m z) in |- *.
assert (Iter (f m) nr z = z).
unfold nr in |- *.
apply Iter_upb_period.
tauto.
tauto.
assert (0 < nr)%nat.
unfold nr in |- *.
apply upb_pos.
tauto.
assert (f_1 m (Iter (f m) nr z) = f_1 m z).
rewrite H0.
tauto.
rewrite <- Iter_f_f_1.
simpl in |- *.
tauto.
tauto.
tauto.
omega.
omega.
intros.
split.
tauto.
intuition.
elim H0.
clear H0.
intros i Hi.
elim Hi.
intros j Hj.
split with i.
split.
omega.
Admitted.

Lemma expo_between_3:forall(m:fmap)(x y z:dart), inv_hmap m -> expo1 m x y -> expo1 m x z -> between m x z y \/ between m (f m y) z (f_1 m x).
Proof.
unfold expo1 in |- *.
unfold between in |- *.
intros.
intuition.
elim H3.
clear H3.
intros i Hi.
elim H4.
intros j Hj.
clear H4.
elim (le_lt_dec j i).
intro.
left.
intros.
split with j.
split with i.
split.
tauto.
split.
tauto.
omega.
intro.
right.
intros.
intuition.
split with (j - i - 1)%nat.
split with (Iter_upb m x - (2 + i))%nat.
assert (Iter_upb m (f m y) = Iter_upb m x).
rewrite <- H5.
assert (Iter (f m) (S i) x = f m (Iter (f m) i x)).
simpl in |- *.
tauto.
rewrite <- H8.
rewrite <- period_uniform.
tauto.
tauto.
tauto.
split.
rewrite <- H5.
assert (f m (Iter (f m) i x) = Iter (f m) (S i) x).
simpl in |- *.
tauto.
rewrite H9.
rewrite <- Iter_comp.
assert (j - i - 1 + S i = j)%nat.
omega.
rewrite H10.
tauto.
split.
rewrite <- H5.
assert (f m (Iter (f m) i x) = Iter (f m) (S i) x).
simpl in |- *.
tauto.
rewrite H9.
rewrite <- Iter_comp.
assert (Iter_upb m x - (2 + i) + S i = Iter_upb m x - 1)%nat.
omega.
rewrite H10.
rewrite <- f_1_Iter_f.
assert (S (Iter_upb m x - 1) = Iter_upb m x)%nat.
omega.
rewrite H11.
rewrite Iter_upb_period.
tauto.
tauto.
tauto.
tauto.
tauto.
rewrite H8.
Admitted.

Lemma succf_dec : forall (m:fmap)(z:dart), {succf m z}+{~succf m z}.
Proof.
intros.
unfold succf in |- *.
elim (pred_dec m one (A_1 m zero z)).
elim (pred_dec m zero z).
tauto.
tauto.
Admitted.

Lemma succf_exd : forall (m:fmap)(z:dart), inv_hmap m -> succf m z -> exd m z.
Proof.
unfold succf in |- *.
intros.
unfold pred in H0.
elim (exd_dec m z).
tauto.
intro.
elim H0.
intros.
clear H0.
elim H1.
apply not_exd_A_1_nil.
tauto.
Admitted.

Lemma predf_dec : forall (m:fmap)(z:dart), {predf m z}+{~predf m z}.
Proof.
unfold predf in |- *.
intros.
generalize (succ_dec m one z).
generalize (succ_dec m zero (A m one z)).
Admitted.

Lemma F_nil : forall m:fmap, inv_hmap m -> F m nil = nil.
Proof.
intros.
unfold F in |- *.
assert (A_1 m zero nil = nil).
apply A_1_nil.
tauto.
rewrite H0.
apply A_1_nil.
Admitted.

Lemma F_1_nil : forall m:fmap, inv_hmap m -> F_1 m nil = nil.
Proof.
intros.
unfold F_1 in |- *.
assert (A m one nil = nil).
apply A_nil.
tauto.
rewrite H0.
apply A_nil.
Admitted.

Lemma succf_exd_F : forall (m:fmap)(z:dart), inv_hmap m -> succf m z -> exd m (F m z).
Proof.
unfold succf in |- *.
unfold F in |- *.
intros.
apply pred_exd_A_1.
tauto.
Admitted.

Lemma predf_exd_F_1 : forall (m:fmap)(z:dart), inv_hmap m -> predf m z -> exd m (F_1 m z).
Proof.
unfold predf in |- *.
unfold F_1 in |- *.
intros.
apply succ_exd_A.
tauto.
Admitted.

Lemma succf_F: forall (m:fmap)(z:dart), inv_hmap m -> (succf m z <-> F m z <> nil).
Proof.
intros.
unfold succf in |- *.
unfold F in |- *.
unfold pred in |- *.
intuition.
rewrite H1 in H0.
apply H0.
apply A_1_nil.
Admitted.

Lemma predf_F_1: forall (m:fmap)(z:dart), inv_hmap m -> (predf m z <-> F_1 m z <> nil).
Proof.
intros.
unfold predf in |- *.
unfold F_1 in |- *.
unfold succ in |- *.
intuition.
rewrite H1 in H0.
apply H0.
apply A_nil.
Admitted.

Lemma not_exd_F_nil : forall (m:fmap)(z:dart), inv_hmap m -> ~exd m z -> F m z = nil.
Proof.
unfold F in |- *.
intros.
apply not_exd_A_1_nil.
tauto.
assert (A_1 m zero z = nil).
apply not_exd_A_1_nil.
tauto.
tauto.
rewrite H1.
apply not_exd_nil.
Admitted.

Lemma not_exd_F_1_nil : forall (m:fmap)(z:dart), inv_hmap m -> ~exd m z -> F_1 m z = nil.
Proof.
unfold F_1 in |- *.
intros.
apply not_exd_A_nil.
tauto.
assert (A m one z = nil).
apply not_exd_A_nil.
tauto.
tauto.
rewrite H1.
apply not_exd_nil.
Admitted.

Lemma F_F_1 : forall (m:fmap)(z:dart), inv_hmap m -> exd m z -> exd m (F_1 m z) -> F m (F_1 m z) = z.
Proof.
unfold F in |- *; unfold F_1 in |- *.
intros.
rewrite A_1_A.
rewrite A_1_A.
tauto.
tauto.
unfold succ in |- *.
intro.
rewrite H2 in H1.
rewrite A_nil in H1.
absurd (exd m nil).
apply not_exd_nil.
tauto.
tauto.
tauto.
tauto.
unfold succ in |- *.
intro.
rewrite H2 in H1.
absurd (exd m nil).
apply not_exd_nil.
tauto.
Admitted.

Lemma F_1_F : forall (m:fmap)(z:dart), inv_hmap m -> exd m z -> exd m (F m z) -> F_1 m (F m z) = z.
Proof.
unfold F in |- *; unfold F_1 in |- *.
intros.
rewrite A_A_1.
rewrite A_A_1.
tauto.
tauto.
unfold pred in |- *.
intro.
rewrite H2 in H1.
rewrite A_1_nil in H1.
absurd (exd m nil).
apply not_exd_nil.
tauto.
tauto.
tauto.
tauto.
unfold pred in |- *.
intro.
rewrite H2 in H1.
absurd (exd m nil).
apply not_exd_nil.
tauto.
Admitted.

Lemma predf_exd : forall (m:fmap)(z:dart), inv_hmap m -> predf m z -> exd m z.
Proof.
unfold predf in |- *.
intros.
apply succ_exd with one.
tauto.
tauto.
