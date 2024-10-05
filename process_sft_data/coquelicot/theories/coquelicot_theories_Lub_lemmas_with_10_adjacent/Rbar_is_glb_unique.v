Require Import Reals mathcomp.ssreflect.ssreflect.
Require Import Rbar Rcomplements Markov.
Open Scope R_scope.
Definition is_ub_Rbar (E : R -> Prop) (l : Rbar) := forall (x : R), E x -> Rbar_le x l.
Definition is_lb_Rbar (E : R -> Prop) (l : Rbar) := forall (x : R), E x -> Rbar_le l x.
Definition is_lub_Rbar (E : R -> Prop) (l : Rbar) := is_ub_Rbar E l /\ (forall b, is_ub_Rbar E b -> Rbar_le l b).
Definition is_glb_Rbar (E : R -> Prop) (l : Rbar) := is_lb_Rbar E l /\ (forall b, is_lb_Rbar E b -> Rbar_le b l).
Definition Lub_Rbar (E : R -> Prop) := proj1_sig (ex_lub_Rbar E).
Definition Glb_Rbar (E : R -> Prop) := proj1_sig (ex_glb_Rbar E).
Definition Rbar_is_upper_bound (E : Rbar -> Prop) (l : Rbar) := forall x, E x -> Rbar_le x l.
Definition Rbar_is_lower_bound (E : Rbar -> Prop) (l : Rbar) := forall x, E x -> Rbar_le l x.
Definition Rbar_is_lub (E : Rbar -> Prop) (l : Rbar) := Rbar_is_upper_bound E l /\ (forall b : Rbar, Rbar_is_upper_bound E b -> Rbar_le l b).
Definition Rbar_is_glb (E : Rbar -> Prop) (l : Rbar) := Rbar_is_lower_bound E l /\ (forall b : Rbar, Rbar_is_lower_bound E b -> Rbar_le b l).
Definition Rbar_lub (E : Rbar -> Prop) := proj1_sig (Rbar_ex_lub E).
Definition Rbar_glb (E : Rbar -> Prop) := proj1_sig (Rbar_ex_glb E).
Definition Empty (E : R -> Prop) := Lub_Rbar (fun x => x = 0 \/ E x) = Glb_Rbar (fun x => x = 0 \/ E x) /\ Lub_Rbar (fun x => x = 1 \/ E x) = Glb_Rbar (fun x => x = 1 \/ E x).

Lemma Rbar_is_lb_subset (E1 E2 : Rbar -> Prop) (l : Rbar) : (forall x, E1 x -> E2 x) -> (Rbar_is_lower_bound E2 l) -> (Rbar_is_lower_bound E1 l).
Proof.
Admitted.

Lemma Rbar_lub_glb (E : Rbar -> Prop) (l : Rbar) : Rbar_is_lub (fun x => E (Rbar_opp x)) (Rbar_opp l) <-> Rbar_is_glb E l.
Proof.
split ; [intros (ub, lub) | intros (lb, glb)] ; split.
apply Rbar_ub_lb ; auto.
intros b Hb ; generalize (lub _ (proj2 (Rbar_ub_lb _ _) Hb)) ; apply Rbar_opp_le.
apply Rbar_lb_ub ; intros x ; simpl ; repeat rewrite Rbar_opp_involutive ; apply lb.
intros b Hb.
Admitted.

Lemma Rbar_glb_lub (E : Rbar -> Prop) (l : Rbar) : Rbar_is_glb (fun x => E (Rbar_opp x)) (Rbar_opp l) <-> Rbar_is_lub E l.
Proof.
split ; [ intros (lb, glb) | intros (ub, lub)] ; split.
apply Rbar_lb_ub ; auto.
intros b Hb ; generalize (glb _ (proj2 (Rbar_lb_ub _ _) Hb)) ; apply Rbar_opp_le.
apply Rbar_ub_lb ; intro x ; simpl ; repeat rewrite Rbar_opp_involutive ; apply ub.
intros b Hb.
Admitted.

Lemma is_lub_Rbar_correct (E : R -> Prop) (l : Rbar) : is_lub_Rbar E l <-> Rbar_is_lub (fun x => is_finite x /\ E x) l.
Proof.
split => [[Hub Hlub]|[Hub Hlub]].
split ; [ | move => b Hb ; apply Hlub ] ; by apply is_ub_Rbar_correct.
Admitted.

Lemma is_glb_Rbar_correct (E : R -> Prop) (l : Rbar) : is_glb_Rbar E l <-> Rbar_is_glb (fun x => is_finite x /\ E x) l.
Proof.
split => [[Hub Hlub]|[Hub Hlub]].
split ; [ | move => b Hb ; apply Hlub ] ; by apply is_lb_Rbar_correct.
Admitted.

Lemma Rbar_ex_lub (E : Rbar -> Prop) : {l : Rbar | Rbar_is_lub E l}.
Proof.
destruct (EM_dec (E p_infty)) as [Hp|Hp].
exists p_infty ; split.
by case.
intros b Hb.
apply Rbar_not_lt_le.
contradict Hp => H.
apply: Rbar_le_not_lt Hp.
by apply Hb.
destruct (ex_lub_Rbar E) as [l Hl].
exists l ; split.
case => [x | | ] // Hx.
by apply Hl.
intros b Hb.
apply Hl => x Hx.
Admitted.

Lemma Rbar_ex_glb (E : Rbar -> Prop) : {l : Rbar | Rbar_is_glb E l}.
Proof.
destruct (Rbar_ex_lub (fun x => E (Rbar_opp x))) as [l Hl].
exists (Rbar_opp l).
Admitted.

Lemma Rbar_opp_glb_lub (E : Rbar -> Prop) : Rbar_glb (fun x => E (Rbar_opp x)) = Rbar_opp (Rbar_lub E).
Proof.
unfold Rbar_glb ; case (Rbar_ex_glb _) ; simpl ; intros g [Hg Hg'] ; unfold Rbar_lub ; case (Rbar_ex_lub _) ; simpl ; intros l [Hl Hl'] ; apply Rbar_le_antisym.
apply Rbar_opp_le ; rewrite Rbar_opp_involutive ; apply Hl', Rbar_lb_ub ; rewrite Rbar_opp_involutive ; auto.
Admitted.

Lemma Rbar_opp_lub_glb (E : Rbar -> Prop) : Rbar_lub (fun x => E (Rbar_opp x)) = Rbar_opp (Rbar_glb E).
Proof.
unfold Rbar_glb ; case (Rbar_ex_glb _) ; simpl ; intros g (Hg, Hg') ; unfold Rbar_lub ; case (Rbar_ex_lub _) ; simpl ; intros l [Hl Hl'] ; apply Rbar_le_antisym.
apply Hl', Rbar_lb_ub ; rewrite Rbar_opp_involutive ; apply (Rbar_is_lb_subset _ E) ; auto ; intros x ; rewrite Rbar_opp_involutive ; auto.
Admitted.

Lemma Rbar_is_lub_unique (E : Rbar -> Prop) (l : Rbar) : Rbar_is_lub E l -> Rbar_lub E = l.
Proof.
move => H.
rewrite /Rbar_lub.
case: Rbar_ex_lub => l0 H0 /=.
apply Rbar_le_antisym.
apply H0, H.
Admitted.

Lemma Rbar_glb_le_lub (E : Rbar -> Prop) : (exists x, E x) -> Rbar_le (Rbar_glb E) (Rbar_lub E).
Proof.
case => x Hex.
apply Rbar_le_trans with x.
unfold Rbar_glb ; case (Rbar_ex_glb _) ; simpl ; intros g (Hg, _) ; apply Hg ; auto.
Admitted.

Lemma Rbar_is_lub_subset (E1 E2 : Rbar -> Prop) (l1 l2 : Rbar) : (forall x, E1 x -> E2 x) -> (Rbar_is_lub E1 l1) -> (Rbar_is_lub E2 l2) -> Rbar_le l1 l2.
Proof.
intros Hs (_,H1) (H2, _).
Admitted.

Lemma Rbar_is_glb_subset (E1 E2 : Rbar -> Prop) (l1 l2 : Rbar) : (forall x, E2 x -> E1 x) -> (Rbar_is_glb E1 l1) -> (Rbar_is_glb E2 l2) -> Rbar_le l1 l2.
Proof.
intros Hs (H1, _) (_, H2).
Admitted.

Lemma Rbar_is_lub_eq (E1 E2 : Rbar -> Prop) (l1 l2 : Rbar) : (forall x, E1 x <-> E2 x) -> (Rbar_is_lub E1 l1) -> (Rbar_is_lub E2 l2) -> l1 = l2.
Proof.
Admitted.

Lemma Rbar_is_glb_eq (E1 E2 : Rbar -> Prop) (l1 l2 : Rbar) : (forall x, E1 x <-> E2 x) -> (Rbar_is_glb E1 l1) -> (Rbar_is_glb E2 l2) -> l1 = l2.
Proof.
Admitted.

Lemma Rbar_is_lub_ext (E1 E2 : Rbar -> Prop) (l : Rbar) : (forall x, E1 x <-> E2 x) -> (Rbar_is_lub E1 l) -> (Rbar_is_lub E2 l).
Proof.
intros Heq (H1,H2) ; split.
apply (Rbar_is_ub_subset _ E1) ; auto ; intros x Hx ; apply Heq ; auto.
Admitted.

Lemma Rbar_is_glb_ext (E1 E2 : Rbar -> Prop) (l : Rbar) : (forall x, E1 x <-> E2 x) -> (Rbar_is_glb E1 l) -> (Rbar_is_glb E2 l).
Proof.
intros Heq (H1, H2) ; split.
apply (Rbar_is_lb_subset _ E1) ; auto ; intros x Hx ; apply Heq ; auto.
Admitted.

Lemma Rbar_lub_subset (E1 E2 : Rbar -> Prop) : (forall x, E1 x -> E2 x) -> Rbar_le (Rbar_lub E1) (Rbar_lub E2).
Proof.
Admitted.

Lemma Rbar_glb_subset (E1 E2 : Rbar -> Prop) : (forall x, E2 x -> E1 x) -> Rbar_le (Rbar_glb E1) (Rbar_glb E2).
Proof.
Admitted.

Lemma Rbar_lub_rw (E1 E2 : Rbar -> Prop) : (forall x, E1 x <-> E2 x) -> Rbar_lub E1 = Rbar_lub E2.
Proof.
Admitted.

Lemma Rbar_is_glb_unique (E : Rbar -> Prop) (l : Rbar) : Rbar_is_glb E l -> Rbar_glb E = l.
Proof.
move => H.
rewrite /Rbar_glb.
case: Rbar_ex_glb => l0 H0 /=.
apply Rbar_le_antisym.
apply H, H0.
apply H0, H.
