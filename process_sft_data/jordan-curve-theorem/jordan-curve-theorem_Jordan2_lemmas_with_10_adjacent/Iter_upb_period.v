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

Lemma diff_int_le:forall(m:fmap)(z:dart)(a b:nat), (b <= a)%nat -> diff_int m z a b.
Proof.
intros.
unfold diff_int in |- *.
intros.
Admitted.

Lemma diff_int_dec:forall(m:fmap)(z:dart)(a b:nat), {diff_int m z a b} + {~diff_int m z a b}.
Proof.
intros.
induction b.
left.
unfold diff_int in |- *.
intros.
omega.
elim IHb.
intro.
generalize (diff_int_aux_dec m z a b (Iter (f m) (S b) z)).
intros.
elim H.
intro.
clear IHb H.
left.
unfold diff_int in |- *.
intros.
unfold diff_int in a0.
unfold diff_int_aux in a1.
elim (eq_nat_dec j (S b)).
intro.
rewrite a2.
apply a1.
omega.
intro.
apply a0.
omega.
intro.
clear IHb H.
unfold diff_int_aux in b0.
right.
unfold diff_int in |- *.
intro.
apply b0.
intros.
apply H.
omega.
intro.
unfold diff_int in b0.
right.
unfold diff_int in |- *.
intro.
apply b0.
intros.
apply H.
Admitted.

Lemma exds_int_gt:forall(m:fmap)(z:dart)(a b:nat)(s:set), (b < a)%nat -> exds_int m z a b s.
Proof.
intros.
unfold exds_int in |- *.
intros.
absurd (b < a)%nat.
omega.
Admitted.

Lemma exds_int_dec : forall(m:fmap)(z:dart)(a b:nat)(s:set), {exds_int m z a b s} + {~exds_int m z a b s}.
Proof.
intros.
elim (le_gt_dec a b).
intro.
induction b.
elim (exds_dec s z).
intro.
left.
unfold exds_int in |- *.
intros.
assert (i = 0)%nat.
omega.
rewrite H0.
simpl in |- *.
tauto.
intro.
right.
unfold exds_int in |- *.
intro.
apply b.
assert (exds s (Iter (f m) 0%nat z)).
apply H.
omega.
simpl in H0.
tauto.
elim (eq_nat_dec a (S b)).
intro.
rewrite <- a1.
elim (exds_dec s (Iter (f m) a z)).
intro.
left.
unfold exds_int in |- *.
intros.
assert (i = a).
omega.
rewrite H0.
tauto.
intro.
right.
unfold exds_int in |- *.
intro.
apply b0.
apply H.
omega.
intro.
assert (a <= b)%nat.
omega.
elim (IHb H).
intro.
elim (exds_dec s (Iter (f m) (S b) z)).
intro.
left.
unfold exds_int in |- *.
intros.
elim (eq_nat_dec i (S b)).
intro.
rewrite a3.
tauto.
intro.
unfold exds_int in a1.
apply a1.
omega.
intro.
right.
unfold exds_int in |- *.
intro.
apply b1.
apply H0.
omega.
intro.
right.
unfold exds_int in |- *.
intro.
apply b1.
unfold exds_int in |- *.
intros.
apply H0.
omega.
intro.
left.
apply exds_int_gt.
Admitted.

Lemma rem_1_step :forall(m:fmap)(z:dart)(s:set), inv_hmap m -> let sr:= Iter_rem_aux m z s in let nr:= Iter_upb_aux m z s in (card sr + 1 <= card s <-> exds s (Iter (f m) (ndN m - card s) z))%nat.
Proof.
simpl in |- *.
intros.
generalize (Iter_rem_aux_equation m z s).
simpl in |- *.
intro.
split.
intro.
generalize H0.
elim (exds_dec s (Iter (f m) (ndN m - card s) z)).
tauto.
intros.
rewrite H2 in H1.
absurd (card s + 1 <= card s)%nat.
omega.
tauto.
intro.
generalize (LQ2 m z s H1).
intro.
Admitted.

Lemma rem_2_steps :forall(m:fmap)(z:dart)(s:set), inv_hmap m -> let sr:= Iter_rem_aux m z s in let nr:= Iter_upb_aux m z s in (card sr + 2 <= card s -> exds (Ds s (Iter (f m) (ndN m - card s) z)) (Iter (f m) (ndN m + 1 - card s) z))%nat.
Proof.
intros.
generalize (rem_1_step m z (Ds s (Iter (f m) (ndN m - card s)%nat z)) H).
simpl in |- *.
generalize (rem_1_step m z s H).
simpl in |- *.
intros.
assert (card (Iter_rem_aux m z s) + 1 <= card s)%nat.
unfold sr in H0.
clear H1 H2.
omega.
assert (exds s (Iter (f m) (ndN m - card s)%nat z)).
tauto.
generalize (Iter_rem_aux_equation m z s).
simpl in |- *.
elim (exds_dec s (Iter (f m) (ndN m - card s) z)).
intros.
assert (card (Ds s (Iter (f m) (ndN m - card s) z)) + 1 = card s)%nat.
rewrite exds_card_Ds.
clear H1 H2 H3 H4 a H5.
omega.
tauto.
assert (card (Ds s (Iter (f m) (ndN m - card s) z)) = card s - 1)%nat.
clear H1 H2 H3 H4 a H5.
omega.
unfold sr in H0.
rewrite H7 in H2.
rewrite <- H5 in H2.
assert (card (Iter_rem_aux m z s) + 1 <= card s - 1)%nat.
clear H1 H2 H3 H4 a H5 H6 H7.
omega.
assert (ndN m + 1 - card s = ndN m - (card s - 1))%nat.
clear H1 H2 H3 H4 a H5 H6 H7 H8.
omega.
rewrite <- H9 in H2.
tauto.
Admitted.

Lemma LP6:forall(m:fmap)(z:dart)(s:set), inv_hmap m -> (card s <= ndN m -> let n0:= ndN m - card s in let nr:= Iter_upb_aux m z s in exds s (Iter (f m) n0 z) -> exds_int m z n0 (nr - 1) s)%nat.
Proof.
intros m z.
refine (well_founded_ind Rs_wf (P6 m z) _).
unfold P6 in |- *.
unfold Iter_upb_aux in |- *.
intros.
generalize (LQ1 m z x).
intro.
generalize (Iter_rem_aux_equation m z x).
simpl in |- *.
intro.
rewrite H4.
generalize H4.
simpl in |- *.
elim (exds_dec x (Iter (f m) (ndN m - card x) z)).
intros.
clear H4.
generalize (exds_card_Ds x (Iter (f m) (ndN m - card x)%nat z) a).
intro.
generalize (H (Ds x (Iter (f m) (ndN m - card x)%nat z))).
intros.
generalize (rem_1_step m z x H0).
simpl in |- *.
intros.
assert (card (Iter_rem_aux m z x) + 1 <= card x)%nat.
tauto.
clear H7.
elim (eq_nat_dec (card (Iter_rem_aux m z x) + 1) (card x))%nat.
intro.
rewrite <- H5.
assert (ndN m - card (Iter_rem_aux m z x) - 1 = ndN m - card x)%nat.
clear H3 H4 H8.
omega.
rewrite H7.
unfold exds_int in |- *.
intros.
assert (i = ndN m - card x)%nat.
clear H1 H3 H4 H8 a0 H7.
omega.
rewrite H10.
tauto.
intro.
assert (card (Iter_rem_aux m z x) + 2 <= card x)%nat.
clear H1 H3 H4.
omega.
generalize (rem_2_steps m z x H0 H7).
intro.
rewrite H4 in H6.
assert (ndN m - (card x - 1) = ndN m + 1 - card x)%nat.
clear H3 H4 H5 H8 b.
omega.
rewrite H10 in H6.
rewrite <- H5.
rewrite <- H5 in H6.
unfold exds_int in |- *.
intros.
elim (eq_nat_dec (ndN m - card x) i)%nat.
intro.
rewrite <- a0.
tauto.
intro.
assert (exds_int m z (ndN m + 1 - card x) (ndN m - card (Iter_rem_aux m z x) - 1) (Ds x (Iter (f m) (ndN m - card x) z)))%nat.
apply H6.
unfold Rs in |- *.
clear H1 H3 H5 H8 b H10 H11 b0.
omega.
tauto.
clear H3 H5 H4 H8 H7 H10 H11 b0.
omega.
tauto.
unfold exds_int in H12.
assert (exds (Ds x (Iter (f m) (ndN m - card x) z)) (Iter (f m) i z))%nat.
apply H12.
clear H10.
clear H1 H3 H5 H4 H8 H7 H8 b.
omega.
eapply exds_Ds_exds.
apply H13.
Admitted.

Lemma LP7:forall(m:fmap)(z:dart)(s:set), inv_hmap m -> (card s <= ndN m -> let n0:= ndN m - card s in let nr:= Iter_upb_aux m z s in exds s (Iter (f m) n0 z) -> forall j:nat, n0 < j <= nr - 1 -> Iter (f m) n0 z <> Iter (f m) j z)%nat.
Proof.
intros m z.
refine (well_founded_ind Rs_wf (P7 m z) _).
unfold P7 in |- *.
unfold Iter_upb_aux in |- *.
intros.
generalize (LQ1 m z x).
generalize (rem_1_step m z x H0).
simpl in |- *.
intro.
assert (card (Iter_rem_aux m z x) + 1 <= card x)%nat.
tauto.
clear H4.
intro.
clear H4.
elim (eq_nat_dec (card (Iter_rem_aux m z x) + 1) (card x))%nat.
intro.
clear H5.
omega.
intro.
assert (card (Iter_rem_aux m z x) + 2 <= card x)%nat.
omega.
generalize (rem_2_steps m z x H0 H4).
intro.
clear b H5.
elim (eq_dart_dec (Iter (f m) (ndN m - card x) z) (Iter (f m) (ndN m - card (Iter_rem_aux m z x) - 1) z))%nat.
intros.
assert (card (Ds x (Iter (f m) (ndN m - card x) z)) = card x - 1)%nat.
rewrite exds_card_Ds.
tauto.
tauto.
assert (card (Ds x (Iter (f m) (ndN m - card x) z)) <= ndN m)%nat.
omega.
generalize (LP6 m z (Ds x (Iter (f m) (ndN m - card x) z)) H0 H7)%nat.
simpl in |- *.
intros.
rewrite H5 in H8.
unfold Iter_upb_aux in H8.
generalize (Iter_rem_aux_equation m z x).
simpl in |- *.
elim (exds_dec x (Iter (f m) (ndN m - card x) z)).
intros.
clear a0.
rewrite <- H9 in H8.
assert (ndN m - (card x - 1) = ndN m + 1 - card x)%nat.
clear H3 a H5 H7 H9.
omega.
rewrite H10 in H8.
generalize (H8 H6).
intro.
clear H8.
unfold exds_int in H11.
assert (exds (Ds x (Iter (f m) (ndN m - card x) z)) (Iter (f m) (ndN m - card (Iter_rem_aux m z x) - 1) z))%nat.
apply H11.
split.
clear H3 a H H7 H9 H10.
omega.
apply le_refl.
rewrite <- a in H8.
absurd (exds (Ds x (Iter (f m) (ndN m - card x) z)) (Iter (f m) (ndN m - card x) z))%nat.
apply not_exds_Ds.
tauto.
tauto.
intros.
elim (eq_nat_dec (ndN m - card (Iter_rem_aux m z x) - 1) j)%nat.
intro.
rewrite <- a.
tauto.
intro.
generalize (H (Ds x (Iter (f m) (ndN m - card x) z)))%nat.
intro.
assert (forall j : nat, ndN m - card (Ds x (Iter (f m) (ndN m - card x) z)) < j <= ndN m - card (Iter_rem_aux m z (Ds x (Iter (f m) (ndN m - card x) z))) - 1 -> Iter (f m) (ndN m - card (Ds x (Iter (f m) (ndN m - card x) z))) z <> Iter (f m) j z)%nat.
apply H5.
unfold Rs in |- *.
rewrite exds_card_Ds.
clear H1 H3 b b0.
omega.
tauto.
tauto.
generalize (exds_card_Ds x (Iter (f m) (ndN m - card x) z) H2)%nat.
intro.
rewrite H7.
clear H3 H4 b b0 H7.
omega.
generalize (exds_card_Ds x (Iter (f m) (ndN m - card x) z) H2)%nat.
intro.
rewrite H7.
assert (ndN m - (card x - 1) = ndN m + 1 - card x)%nat.
clear H3 b b0 H7.
omega.
rewrite H8.
tauto.
clear H5.
generalize (exds_card_Ds x (Iter (f m) (ndN m - card x) z) H2)%nat.
intro.
rewrite H5 in H7.
generalize (Iter_rem_aux_equation m z x).
simpl in |- *.
elim (exds_dec x (Iter (f m) (ndN m - card x) z))%nat.
intros.
clear a.
rewrite <- H8 in H7.
assert (ndN m - (card x - 1) = ndN m + 1 - card x)%nat.
clear H3 b b0 H5 H8.
omega.
rewrite H9 in H7.
intro.
assert (Iter (f m) (S (ndN m - card x)) z = Iter (f m) (S j) z)%nat.
simpl in |- *.
rewrite H10.
tauto.
generalize H11.
assert (S (ndN m - card x) = ndN m + 1 - card x)%nat.
clear H9.
clear H5.
clear H3 b b0 H8 H10 H11.
omega.
rewrite H12.
apply H7.
split.
rewrite <- H12.
apply lt_n_S.
tauto.
clear H12.
clear H9.
clear H5.
clear H4.
clear H1 b H8 H10 H11.
elim H3.
intros.
clear H1.
clear H3.
omega.
Admitted.

Lemma LP8:forall(m:fmap)(z:dart)(s:set), inv_hmap m -> (card s <= ndN m -> let n0:= ndN m - card s in let nr:= Iter_upb_aux m z s in exds s (Iter (f m) n0 z) -> diff_int m z n0 (nr - 1))%nat.
Proof.
intros m z.
refine (well_founded_ind Rs_wf (P8 m z) _).
unfold P8 in |- *.
unfold Iter_upb_aux in |- *.
intros.
generalize (rem_1_step m z x H0).
simpl in |- *.
intro.
assert (card (Iter_rem_aux m z x) + 1 <= card x)%nat.
tauto.
clear H3.
elim (eq_nat_dec (card (Iter_rem_aux m z x) + 1) (card x))%nat.
intro.
clear H4.
assert (ndN m - card (Iter_rem_aux m z x) - 1 = ndN m - card x)%nat.
omega.
rewrite H3.
apply diff_int_le.
apply le_refl.
intro.
assert (card (Iter_rem_aux m z x) + 2 <= card x)%nat.
omega.
clear b H4.
generalize (rem_2_steps m z x H0 H3).
intro.
generalize (LP7 m z x H0 H1 H2).
intro.
unfold diff_int in |- *.
intros.
elim (eq_nat_dec (ndN m - card x) i)%nat.
intro.
rewrite <- a.
unfold Iter_upb_aux in H5.
apply H5.
split.
rewrite a.
tauto.
tauto.
intro.
assert (card (Ds x (Iter (f m) (ndN m - card x) z)) = card x - 1)%nat.
rewrite exds_card_Ds.
tauto.
tauto.
generalize (Iter_rem_aux_equation m z x).
simpl in |- *.
elim (exds_dec x (Iter (f m) (ndN m - card x) z))%nat.
intros.
clear a.
clear H5.
generalize (H (Ds x (Iter (f m) (ndN m - card x) z)))%nat.
intros.
assert (diff_int m z (ndN m - card (Ds x (Iter (f m) (ndN m - card x) z))) (ndN m - card (Iter_rem_aux m z (Ds x (Iter (f m) (ndN m - card x) z))) - 1))%nat.
apply H5.
unfold Rs in |- *.
apply exds_card_Ds_inf.
tauto.
tauto.
rewrite H7.
omega.
rewrite H7.
assert (ndN m - (card x - 1) = ndN m + 1 - card x)%nat.
clear H5.
clear H.
clear H8.
omega.
rewrite H9.
tauto.
clear H5 H.
rewrite <- H8 in H9.
unfold diff_int in H9.
rewrite H7 in H9.
apply H9.
split.
clear H8 H9.
clear H1 H3 H4.
clear H0.
omega.
tauto.
Admitted.

Theorem exd_diff_orb:forall(m:fmap)(z:dart), inv_hmap m -> exd m z -> diff_orb m z.
intros.
unfold diff_orb in |- *.
generalize (nd_card m).
intro.
assert (ndN m - card (fmap_to_set m) = 0)%nat.
rewrite H1.
omega.
cut (diff_int m z (ndN m - card (fmap_to_set m)) (Iter_upb_aux m z (fmap_to_set m) - 1))%nat.
rewrite H2.
tauto.
apply LP8.
tauto.
rewrite H1.
apply le_refl.
rewrite H2.
simpl in |- *.
generalize (exd_exds m z).
Admitted.

Lemma Iter_period:forall(m:fmap)(z:dart)(i n:nat), inv_hmap m -> exd m z -> let p:= Iter_upb m z in Iter (f m) (i + n*p)%nat z = Iter (f m) i z.
Proof.
intros.
intros.
assert (Iter (f m) p z = z).
unfold p in |- *.
apply Iter_upb_period.
tauto.
tauto.
rewrite Iter_plus_mult.
trivial.
assumption.
assumption.
Admitted.

Lemma mod_p:forall(m:fmap)(z:dart)(i:nat), inv_hmap m -> exd m z -> let p := Iter_upb m z in {j :nat | Iter (f m) i z = Iter (f m) j z /\ (j < p)%nat}.
Proof.
intros.
assert (p > 0)%nat.
unfold p in |- *.
generalize (upb_pos m z H0).
intro.
omega.
generalize (modulo p H1 i).
intro.
elim H2.
intros r Hr.
split with r.
elim Hr.
intros q Hq.
elim Hq.
clear Hq.
intros.
split.
rewrite H3.
rewrite plus_comm.
unfold p in |- *.
rewrite Iter_period.
trivial.
tauto.
tauto.
Admitted.

Lemma period_uniform : forall(m:fmap)(z:dart)(i:nat), inv_hmap m -> exd m z -> Iter_upb m z = Iter_upb m (Iter (f m) i z).
Proof.
intros.
set (zi := Iter (f m) i z) in |- *.
set (p := Iter_upb m z) in |- *.
set (q := Iter_upb m zi) in |- *.
generalize (Iter_upb_period m z H H0).
simpl in |- *.
fold p in |- *.
intro.
assert (exd m zi).
unfold zi in |- *.
generalize (exd_Iter_f m i z H).
tauto.
generalize (Iter_upb_period m zi H H2).
simpl in |- *.
fold q in |- *.
intro.
assert (Iter (f m) (i + q)%nat z = Iter (f m) q zi).
unfold zi in |- *.
rewrite plus_comm.
apply Iter_comp.
assert (Iter (f m) q z = z).
apply (Iter_plus m z q i H H0).
fold zi in |- *.
rewrite plus_comm.
rewrite <- H3.
tauto.
assert (Iter (f m) p zi = zi).
unfold zi in |- *.
rewrite <- Iter_comp.
rewrite plus_comm.
assert (i + p = i + 1 * p)%nat.
omega.
rewrite H6.
unfold p in |- *.
rewrite Iter_period.
trivial.
trivial.
trivial.
clear H4.
elim (lt_eq_lt_dec p q).
intro.
elim a.
clear a.
intro.
generalize (exd_diff_orb m zi H H2).
unfold diff_orb in |- *.
unfold Iter_upb in q.
unfold Iter_rem in q.
unfold Iter_upb_aux in |- *.
fold q in |- *.
unfold diff_int in |- *.
intros.
absurd (Iter (f m) p zi = zi).
intro.
symmetry in H7.
replace zi with (Iter (f m) 0%nat zi) in H7.
generalize H7.
clear H7.
apply H4.
split.
omega.
split.
unfold p in |- *.
apply upb_pos.
tauto.
omega.
simpl in |- *.
trivial.
tauto.
tauto.
intro.
generalize (exd_diff_orb m z H H0).
unfold diff_orb in |- *.
unfold Iter_upb in p.
unfold Iter_rem in p.
unfold Iter_upb_aux in |- *.
fold p in |- *.
unfold diff_int in |- *.
intros.
symmetry in H5.
absurd (z = Iter (f m) q z).
replace z with (Iter (f m) 0%nat z).
apply H4.
split.
omega.
split.
unfold q in |- *.
apply upb_pos.
tauto.
omega.
simpl in |- *.
trivial.
Admitted.

Lemma unicity_mod_p:forall(m:fmap)(z:dart)(j k:nat), inv_hmap m -> exd m z -> let p := Iter_upb m z in (j < p)%nat -> (k < p)%nat -> Iter (f m) j z = Iter (f m) k z -> j = k.
Proof.
intros.
generalize (exd_diff_orb m z H H0).
unfold diff_orb in |- *.
unfold Iter_upb in p.
unfold Iter_upb_aux in |- *.
unfold Iter_rem in p.
fold p in |- *.
unfold diff_int in |- *.
intros.
elim (le_gt_dec j k).
elim (eq_nat_dec j k).
intros.
tauto.
intros.
absurd (Iter (f m) j z = Iter (f m) k z).
apply (H4 j k).
omega.
tauto.
intro.
symmetry in H3.
absurd (Iter (f m) k z = Iter (f m) j z).
apply (H4 k j).
omega.
Admitted.

Lemma expo_expo1: forall(m:fmap)(z t:dart), inv_hmap m -> (expo m z t <-> expo1 m z t).
Proof.
unfold expo in |- *.
unfold expo1 in |- *.
intros.
unfold expo in |- *.
unfold expo1 in |- *.
intros.
split.
intros.
elim H0.
clear H0.
intros.
split.
tauto.
elim H1.
intros i Hi.
clear H1.
generalize (mod_p m z i H H0).
simpl in |- *.
intros.
elim H1.
intros j Hj.
split with j.
split.
tauto.
rewrite Hi in Hj.
symmetry in |- *.
tauto.
intros.
elim H0.
clear H0.
intros.
split.
tauto.
elim H1.
intros.
split with x.
Admitted.

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
Admitted.

Lemma expo_exd: forall(m:fmap)(z t:dart), inv_hmap m -> expo m z t -> exd m t.
Proof.
unfold expo in |- *.
intros.
decompose [and] H0.
elim H2.
intros i Hi.
rewrite <- Hi.
generalize (exd_Iter_f m i z).
Admitted.

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

Theorem Iter_upb_period:forall(m:fmap)(z:dart), inv_hmap m -> exd m z -> let nr:= Iter_upb m z in Iter (f m) nr z = z.
Proof.
simpl in |- *.
intros.
generalize (ex_i_upb m z H H0).
simpl in |- *.
intros.
elim H1.
intros i Hi.
clear H1.
elim (eq_nat_dec i 0%nat).
intro.
rewrite a in Hi.
simpl in Hi.
symmetry in |- *.
tauto.
intro.
decompose [and] Hi.
clear Hi.
assert (f_1 m (Iter (f m) i z) = f_1 m (Iter (f m) (Iter_upb m z) z)).
rewrite H2.
tauto.
set (i1 := (i - 1)%nat) in |- *.
set (nr1 := (Iter_upb m z - 1)%nat) in |- *.
assert (i = S i1).
unfold i1 in |- *.
omega.
assert (Iter_upb m z = S nr1).
unfold nr1 in |- *.
omega.
rewrite H5 in H3.
rewrite H4 in H3.
simpl in H3.
rewrite f_1_f in H3.
rewrite f_1_f in H3.
unfold i1 in H3.
unfold nr1 in H3.
absurd (Iter (f m) (i - 1)%nat z = Iter (f m) (Iter_upb m z - 1)%nat z).
generalize (LP8 m z (fmap_to_set m) H).
simpl in |- *.
intros.
unfold diff_int in H6.
assert (forall i j : nat, ndN m - card (fmap_to_set m) <= i /\ i < j <= Iter_upb_aux m z (fmap_to_set m) - 1 -> Iter (f m) i z <> Iter (f m) j z)%nat.
apply H6.
rewrite nd_card.
apply le_refl.
assert (ndN m - card (fmap_to_set m) = 0)%nat.
rewrite nd_card.
simpl in |- *.
omega.
rewrite H7.
simpl in |- *.
generalize (exd_exds m z).
tauto.
apply H7.
split.
clear H6.
clear H7.
clear H2.
rewrite nd_card.
omega.
clear H7 H6.
clear H2.
split.
omega.
unfold Iter_upb in |- *.
unfold Iter_upb_aux in |- *.
unfold Iter_rem in |- *.
apply le_refl.
tauto.
tauto.
generalize (exd_Iter_f m nr1 z).
tauto.
tauto.
generalize (exd_Iter_f m i1 z).
tauto.
