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

Lemma Rbar_glb_rw (E1 E2 : Rbar -> Prop) : (forall x, E1 x <-> E2 x) -> Rbar_glb E1 = Rbar_glb E2.
Proof.
Admitted.

Lemma Empty_correct_2 (E : R -> Prop) : (forall x, ~ E x) -> Empty E.
Proof.
move => H ; split ; rewrite /Glb_Rbar /Lub_Rbar ; [ case : (ex_lub_Rbar (fun x : R => x = 0 \/ E x)) => s0 Hs0 ; case : (ex_glb_Rbar (fun x : R => x = 0 \/ E x)) => i0 Hi0 /= | case : (ex_lub_Rbar (fun x : R => x = 1 \/ E x)) => s1 Hs1 ; case : (ex_glb_Rbar (fun x : R => x = 1 \/ E x)) => i1 Hi1 /=].
have : (i0 = Finite 0) ; last move => -> ; apply: Rbar_le_antisym.
apply Hi0 ; by left.
apply Hi0 => y ; case => H0.
rewrite H0 ; by right.
contradict H0 ; apply H.
apply Hs0 => y ; case => H0.
rewrite H0 ; by right.
contradict H0 ; apply H.
apply Hs0 ; by left.
have : (i1 = Finite 1) ; last move => -> ; apply: Rbar_le_antisym.
apply Hi1 ; by left.
apply Hi1 => y ; case => H1.
rewrite H1 ; by right.
contradict H1 ; apply H.
apply Hs1 => y ; case => H1.
rewrite H1 ; by right.
contradict H1 ; apply H.
Admitted.

Lemma Empty_dec (E : R -> Prop) : {~Empty E}+{Empty E}.
Proof.
case: (Rbar_eq_dec (Lub_Rbar (fun x => x = 0 \/ E x)) (Glb_Rbar (fun x => x = 0 \/ E x))) => H0 ; [ | left].
case: (Rbar_eq_dec (Lub_Rbar (fun x => x = 1 \/ E x)) (Glb_Rbar (fun x => x = 1 \/ E x))) => H1 ; [by right | left].
contradict H1 ; apply H1.
Admitted.

Lemma not_Empty_dec (E : R -> Prop) : (Decidable.decidable (exists x, E x)) -> {(exists x, E x)} + {(forall x, ~ E x)}.
Proof.
move => He ; case: (Empty_dec E) => Hx ; [left|right].
case: He => // He.
contradict Hx ; apply: Empty_correct_2 => x ; contradict He ; by exists x.
Admitted.

Lemma uniqueness_dec P : (exists ! x : R, P x) -> {x : R | P x}.
Proof.
move => H.
exists (Lub_Rbar P).
case: H => x Hx.
replace (real (Lub_Rbar P)) with (real (Finite x)).
by apply Hx.
apply f_equal, sym_eq, is_lub_Rbar_unique.
split.
move => y Hy.
right ; by apply sym_eq, Hx.
move => b Hb.
Admitted.

Lemma Empty_correct_1 (E : R -> Prop) : Empty E -> forall x, ~ E x.
Proof.
case => E0 E1 x Ex.
rewrite /Lub_Rbar /Glb_Rbar in E0 ; case : (ex_lub_Rbar (fun x : R => x = 0 \/ E x)) E0 => /= s0 Hs0 ; case : (ex_glb_Rbar (fun x : R => x = 0 \/ E x)) => i0 Hi0 /= E0.
have : (x = 0) ; last move => {s0 Hs0 i0 Hi0 E0}.
apply Rle_antisym.
apply (Rbar_le_trans x s0 0).
apply Hs0 ; by right.
rewrite E0 ; apply Hi0 ; by left.
apply (Rbar_le_trans 0 s0 x).
apply Hs0 ; by left.
rewrite E0 ; apply Hi0 ; by right.
rewrite /Lub_Rbar /Glb_Rbar in E1 ; case : (ex_lub_Rbar (fun x : R => x = 1 \/ E x)) E1 => /= s1 Hs1 ; case : (ex_glb_Rbar (fun x : R => x = 1 \/ E x)) => i1 Hi1 /= E1.
have : (x = 1) ; last move => {s1 Hs1 i1 Hi1 E1}.
apply Rle_antisym.
apply (Rbar_le_trans x s1 1).
apply Hs1 ; by right.
rewrite E1 ; apply Hi1 ; by left.
apply (Rbar_le_trans 1 s1 x).
apply Hs1 ; by left.
rewrite E1 ; apply Hi1 ; by right.
move => -> ; apply R1_neq_R0.
