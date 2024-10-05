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

Lemma expo_refl: forall(m:fmap)(z:dart), exd m z -> expo m z z.
Proof.
intros.
unfold expo in |- *.
split.
tauto.
split with 0%nat.
simpl in |- *.
Admitted.

Lemma expo_trans: forall(m:fmap)(z t u:dart), expo m z t -> expo m t u -> expo m z u.
Proof.
unfold expo in |- *.
intros.
intuition.
elim H2.
intros j Hj.
elim H3.
intros i Hi.
split with (i + j)%nat.
rewrite Iter_comp.
rewrite Hj.
Admitted.

Lemma expo_symm:forall(m:fmap)(z t:dart), inv_hmap m -> expo m z t -> expo m t z.
Proof.
intros m z t Hm He.
assert (exd m t).
apply expo_exd with z.
tauto.
tauto.
unfold expo in |- *.
unfold expo in He.
intuition.
elim H1.
intros i Hi.
rewrite <- Hi.
clear H1.
generalize (mod_p m z i Hm H0).
intro.
simpl in H1.
elim H1.
intros r Hr.
elim Hr.
clear Hr H1.
intros.
split with (Iter_upb m z - r)%nat.
rewrite H1.
rewrite <- Iter_comp.
assert (Iter_upb m z - r + r = Iter_upb m z)%nat.
omega.
rewrite H3.
apply Iter_upb_period.
tauto.
Admitted.

Lemma ex_j_dec: forall(m:fmap)(z t:dart)(n:nat), {ex_j m z t n} + {~ex_j m z t n}.
Proof.
induction n.
simpl in |- *.
apply eq_dart_dec.
simpl in |- *.
generalize (eq_dart_dec (f m (Iter (f m) n z)) t).
Admitted.

Lemma ex_j_exist_j:forall(m:fmap)(z t:dart)(n:nat), ex_j m z t n <-> exists j :nat, (j <= n)%nat /\ Iter (f m) j z = t.
Proof.
induction n.
simpl in |- *.
split.
intro.
split with 0%nat.
split.
omega.
simpl in |- *.
tauto.
intro.
elim H.
intros j Hj.
intuition.
inversion H0.
rewrite H2 in H1.
simpl in |- *.
simpl in H1.
tauto.
simpl in |- *.
split.
intro.
elim H.
intro.
split with (S n).
split.
clear IHn H H0.
omega.
simpl in |- *.
tauto.
intro.
assert (exists j : nat, (j <= n)%nat /\ Iter (f m) j z = t).
tauto.
elim H1.
intros j Hj.
split with j.
split.
decompose [and] Hj.
clear H H0 H1 Hj H3 IHn.
omega.
tauto.
intros.
elim H.
intros j Hj.
elim (eq_nat_dec j (S n)).
intro.
rewrite a in Hj.
simpl in Hj.
tauto.
intro.
assert (exists j : nat, (j <= n)%nat /\ Iter (f m) j z = t).
split with j.
split.
clear IHn.
omega.
tauto.
Admitted.

Lemma expo1_ex_j: forall(m:fmap)(z t:dart), inv_hmap m -> exd m z -> let p:= Iter_upb m z in (ex_j m z t (p - 1)%nat <-> expo1 m z t).
Proof.
intros.
generalize (Iter_upb_period m z H H0).
generalize (upb_pos m z H0).
rename H into hm.
rename H0 into hz.
fold p in |- *.
intros Hp1 Hp2.
generalize (ex_j_exist_j m z t (p - 1)%nat).
unfold expo1 in |- *.
fold p in |- *.
intros.
split.
intro.
assert (exists j : nat, (j <= p - 1)%nat /\ Iter (f m) j z = t).
tauto.
elim H1.
intros j Hj.
split.
tauto.
split with j.
split.
clear H H0.
omega.
tauto.
intro.
elim H0.
intros.
elim H2.
clear H0 H2.
intros i Hj.
assert (exists j : nat, (j <= p - 1)%nat /\ Iter (f m) j z = t).
split with i.
split.
clear H.
omega.
tauto.
Admitted.

Lemma expo1_dec : forall (m:fmap)(z t:dart), inv_hmap m -> exd m z -> {expo1 m z t} + {~expo1 m z t}.
Proof.
intros.
set (p := Iter_upb m z) in |- *.
generalize (ex_j_dec m z t (p - 1)).
intro.
elim H1.
intro.
left.
generalize (expo1_ex_j m z t H H0).
simpl in |- *.
fold p in |- *.
tauto.
intro.
right.
intro.
generalize (expo1_ex_j m z t H H0).
simpl in |- *.
fold p in |- *.
Admitted.

Lemma expo_dec: forall(m:fmap)(z t:dart), inv_hmap m -> {expo m z t} + {~expo m z t}.
Proof.
intros m z t hm.
generalize (expo_expo1 m z t hm).
generalize (expo1_dec m z t hm).
intros.
elim (exd_dec m z).
tauto.
unfold expo in |- *.
Admitted.

Theorem period_expo : forall(m:fmap)(z t:dart), inv_hmap m -> expo m z t -> Iter_upb m z = Iter_upb m t.
Proof.
unfold expo in |- *.
intros.
elim H0.
clear H0.
intros.
elim H1.
intros i Hi.
rewrite <- Hi.
apply period_uniform.
tauto.
Admitted.

Theorem period_lub : forall(m:fmap)(z:dart), inv_hmap m -> exd m z -> let nr:= Iter_upb m z in 0 < nr /\ Iter (f m) nr z = z /\ forall i:nat, 0 < i < nr -> Iter (f m) i z <> z.
Proof.
intros.
split.
unfold nr in |- *.
apply upb_pos.
tauto.
split.
unfold nr in |- *.
apply Iter_upb_period.
tauto.
tauto.
intros.
generalize (exd_diff_orb m z).
unfold diff_orb in |- *.
unfold Iter_upb in nr.
unfold Iter_rem in nr.
unfold Iter_upb_aux in |- *.
fold nr in |- *.
unfold diff_int in |- *.
intros.
assert (forall i j : nat, 0 <= i /\ i < j <= nr - 1 -> Iter (f m) i z <> Iter (f m) j z).
tauto.
clear H2.
generalize (H3 0 i).
intros.
simpl in H2.
intro.
symmetry in H4.
apply H2.
split.
omega.
omega.
Admitted.

Lemma degree_pos_aux:forall(m:fmap)(z:dart), P_degree_pos m z 1 (degree m z).
Proof.
unfold degree in |- *.
intros.
apply degree_aux_ind.
intros.
unfold P_degree_pos in |- *.
tauto.
intros.
unfold P_degree_pos in |- *.
intros.
omega.
intros.
unfold P_degree_pos in |- *.
unfold P_degree_pos in H.
assert (0 < n + 1).
omega.
tauto.
intros.
unfold P_degree_pos in |- *.
intros.
Admitted.

Theorem degree_pos:forall(m:fmap)(z:dart), exd m z -> 0 < degree m z.
Proof.
unfold degree in |- *.
intros.
generalize (degree_pos_aux m z).
unfold P_degree_pos in |- *.
unfold degree in |- *.
intros.
assert (0 < 1).
omega.
Admitted.

Lemma degree_diff_aux:forall(m:fmap)(z:dart), P_degree_diff m z 1 (degree m z).
Proof.
unfold degree in |- *.
intros.
apply degree_aux_ind.
intros.
unfold P_degree_diff in |- *.
intros.
omega.
intros.
unfold P_degree_diff in |- *.
intros.
rewrite _x1 in H2.
assert (i = n).
rewrite _x1 in |- *.
omega.
rewrite H3 in |- *.
intro.
symmetry in H4.
assert (z <> Iter (f m) n z).
apply _x0.
tauto.
intros.
unfold P_degree_diff in |- *.
unfold P_degree_diff in H.
intros.
elim (eq_nat_dec n i).
intro.
rewrite <- a in |- *.
intro.
assert (z <> Iter (f m) n z).
apply _x0.
symmetry in H4.
tauto.
intro.
apply H.
tauto.
tauto.
omega.
split.
omega.
tauto.
intros.
unfold P_degree_diff in |- *.
intros.
Admitted.

Theorem degree_diff: forall (m:fmap)(z:dart), inv_hmap m -> exd m z -> forall i:nat, 0 < i < (degree m z) -> Iter (f m) i z <> z.
Proof.
intros.
generalize (degree_diff_aux m z).
unfold P_degree_diff in |- *.
intros.
assert (forall i : nat, 1 <= i < degree m z -> Iter (f m) i z <> z).
apply H2.
tauto.
tauto.
omega.
apply H3.
Admitted.

Lemma degree_bound: forall (m:fmap)(z:dart), inv_hmap m -> exd m z -> degree m z <= ndN m.
Proof.
intros.
elim (le_lt_dec (degree m z) (ndN m)).
tauto.
intro.
generalize (degree_diff m z H H0).
intro.
set (nr := Iter_upb m z) in |- *.
assert (Iter (f m) nr z = z).
unfold nr in |- *.
apply Iter_upb_period.
tauto.
tauto.
assert (nr <= ndN m).
unfold nr in |- *.
unfold Iter_upb in |- *.
omega.
absurd (Iter (f m) nr z = z).
apply H1.
split.
unfold nr in |- *.
apply upb_pos.
tauto.
omega.
Admitted.

Lemma degree_per_aux: forall(m:fmap)(z:dart), P_degree_per m z 1 (degree m z).
Proof.
unfold degree in |- *.
intros.
apply degree_aux_ind.
intros.
unfold P_degree_per in |- *.
symmetry in |- *.
tauto.
intros.
unfold P_degree_per in |- *.
intros.
absurd (ndN m + 1 <= ndN m).
omega.
tauto.
intros.
unfold P_degree_per in |- *.
unfold P_degree_per in H.
intros.
apply H.
tauto.
tauto.
omega.
tauto.
intros.
unfold P_degree_per in |- *.
intros.
absurd (ndN m + 1 <= ndN m).
omega.
Admitted.

Theorem degree_per: forall (m:fmap)(z:dart), inv_hmap m -> exd m z -> Iter (f m) (degree m z) z = z.
Proof.
intros.
apply degree_per_aux.
tauto.
tauto.
omega.
apply degree_bound.
tauto.
Admitted.

Theorem degree_lub: forall(m:fmap)(z:dart), inv_hmap m -> exd m z -> let p:= degree m z in 0 < p /\ Iter (f m) p z = z /\ forall i:nat, 0 < i < p -> Iter (f m) i z <> z.
Proof.
intros.
unfold p in |- *.
split.
apply degree_pos.
tauto.
split.
apply degree_per.
tauto.
tauto.
apply degree_diff.
tauto.
Admitted.

Theorem upb_eq_degree:forall(m:fmap)(z:dart), inv_hmap m -> exd m z -> Iter_upb m z = degree m z.
Proof.
intros.
set (p := degree m z) in |- *.
set (nr := Iter_upb m z) in |- *.
generalize (period_lub m z H H0).
generalize (degree_lub m z H H0).
simpl in |- *.
fold p in |- *.
fold nr in |- *.
intros.
decompose [and] H1.
clear H1.
decompose [and] H2.
clear H2.
elim (lt_eq_lt_dec nr p).
intro.
elim a.
intro.
absurd (Iter (f m) nr z = z).
apply H6.
omega.
tauto.
tauto.
intro.
absurd (Iter (f m) p z = z).
apply H8.
omega.
Admitted.

Theorem expo_degree : forall(m:fmap)(z t:dart), inv_hmap m -> expo m z t -> degree m z = degree m t.
Proof.
intros.
generalize (period_expo m z t H H0).
rewrite upb_eq_degree in |- *.
rewrite upb_eq_degree in |- *.
tauto.
tauto.
apply (expo_exd m z t H H0).
tauto.
unfold expo in H0.
Admitted.

Lemma ndN_pos:forall(m:fmap)(z:dart), exd m z -> 0 < ndN m.
Proof.
induction m.
simpl in |- *.
tauto.
simpl in |- *.
intros.
elim (exd_dec m d).
intro.
apply IHm with d.
tauto.
intro.
omega.
simpl in |- *.
tauto.
