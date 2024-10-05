Require Import List Arith Lia Max Wellfounded Setoid Eqdep_dec.
From Undecidability.Shared.Libs.DLW.Utils Require Import utils_tac utils_list finite.
From Undecidability.Shared.Libs.DLW.Vec Require Import pos.
From Undecidability.Shared.Libs.DLW.Wf Require Import wf_finite wf_chains.
From Undecidability.TRAKHTENBROT Require Import notations fol_ops.
Set Implicit Arguments.
Inductive bt : Set := bt_leaf | bt_node : bt -> bt -> bt.
Local Notation "∅" := bt_leaf.
Local Infix "⪧" := bt_node.
Section bt_rect'.
Variables (P : bt -> Type) (HP0 : P ∅) (HP1 : forall x t, P t -> P (x⪧t)).
End bt_rect'.
Fact bt_eq_dec (s t : bt) : { s = t } + { s <> t }.
Proof.
decide equality.
Fact bt_eq_pirr (s t : bt) (H1 H2 : s = t) : H1 = H2.
Proof.
apply UIP_dec, bt_eq_dec.
Fixpoint bt_depth t := match t with | ∅ => 0 | r⪧s => max (S ⌞r⌟) ⌞s⌟ end where "⌞ t ⌟" := (bt_depth t).
Inductive bt_equiv : bt -> bt -> Prop := | in_bte_refl : forall s, s ≈ s | in_bte_sym : forall s t, s ≈ t -> t ≈ s | in_bte_tran : forall r s t, r ≈ s -> s ≈ t -> r ≈ t | in_bte_cntr : forall s t, s⪧s⪧t ≈ s⪧t | in_bte_comm : forall s t u, s⪧t⪧u ≈ t⪧s⪧u | in_bte_cngr : forall s s' t t', s ≈ s' -> t ≈ t' -> s⪧t ≈ s'⪧t' where "s ≈ t" := (bt_equiv s t).
Hint Constructors bt_equiv : core.
Local Notation "s ≉ t" := (~ s ≈ t).
Notation bte_refl := in_bte_refl.
Notation bte_trans := in_bte_tran.
Fact bte_sym x y : x ≈ y <-> y ≈ x.
Proof.
split; auto.
Add Parametric Relation: (bt) (bt_equiv) reflexivity proved by bte_refl symmetry proved by in_bte_sym transitivity proved by bte_trans as bte_rst.
Add Parametric Morphism: (bt_node) with signature (bt_equiv) ==> (bt_equiv) ==> (bt_equiv) as bt_node_congr.
Proof.
intros; auto.
Fact bte_leaf_eq s t : s ≈ t -> (s = ∅ <-> t = ∅).
Proof.
induction 1; try tauto; split; discriminate.
Fact bte_discr s t : s⪧t ≉ ∅.
Proof.
intros H; apply bte_leaf_eq in H.
generalize (proj2 H eq_refl); discriminate.
Fact bte_inv_0 s : s ≈ ∅ <-> s = ∅.
Proof.
split.
+
intros H; destruct s; auto.
apply bte_discr in H; tauto.
+
intros ->; auto.
Definition bt_mem s t := s⪧t ≈ t.
Local Infix "∈" := bt_mem.
Local Notation "s ∉ t" := (~ s ∈ t).
Section establishing_membership_inversion.
Reserved Notation "x ⋷ y" (at level 70, no associativity).
Inductive bt_restr_mem : bt -> bt -> Prop := | in_btrm_0 : forall s t, s ⋷ s⪧t | in_btrm_1 : forall s t u, s ⋷ u -> s ⋷ t⪧u where "s ⋷ t" := (bt_restr_mem s t).
Hint Constructors bt_restr_mem : core.
Fact btrm_inv u s t : u ⋷ s⪧t <-> u = s \/ u ⋷ t.
Proof.
split.
+
inversion 1; auto.
+
intros [ <- | ]; constructor; auto.
Notation "s ≾ t" := (forall u, u ⋷ s -> exists v, v ⋷ t /\ u ≈ v).
Fact bt_rincl_refl s : s ≾ s.
Proof.
intros u; exists u; auto.
Fact bt_rincl_trans r s t : r ≾ s -> s ≾ t -> r ≾ t.
Proof.
intros H1 H2 u Hu.
destruct H1 with (1 := Hu) as (v & Hv & H3).
destruct H2 with (1 := Hv) as (w & ? & ?).
exists w; split; auto.
apply bte_trans with v; auto.
Hint Resolve bt_rincl_refl bt_rincl_trans : core.
Fact btrm_btm s t : s ⋷ t -> s ∈ t.
Proof.
induction 1 as [ | s t u ]; try (constructor; auto; fail).
constructor; apply bte_trans with (t⪧s⪧u); auto.
Hint Resolve btrm_btm : core.
Fact btm_congr_l s t u : s ≈ t -> s ∈ u -> t ∈ u.
Proof.
intros ? H; apply bte_trans with (2 := H); auto.
Fact btm_congr_r s t u : s ≈ t -> u ∈ s -> u ∈ t.
Proof.
intros H1 H2.
apply bte_trans with (2 := H1), bte_trans with (2 := H2); auto.
Fact btm_inv_0 s : s ∈ ∅ <-> False.
Proof.
split; try tauto; apply bte_discr.
Fact btm_inv u s t : u ∈ s⪧t <-> u ≈ s \/ u ∈ t.
Proof.
split.
+
intros H.
destruct (@bte_rincl _ _ H u) as (v & H1 & ?); auto.
revert H1; rewrite btrm_inv; intros [ <- | ]; auto.
right; apply bte_trans with (v⪧t); auto.
apply btrm_btm; auto.
+
intros [ H | H ].
*
apply btm_congr_l with s; auto.
*
apply bte_trans with (1 := in_bte_comm _ _ _); auto.
End establishing_membership_inversion.
Add Parametric Morphism: (bt_mem) with signature (bt_equiv) ==> (bt_equiv) ==> (iff) as bte_congr.
Proof.
intros x y H1 a b H2; split; intros H.
+
apply btm_congr_l with (1 := H1), btm_congr_r with (1 := H2); auto.
+
rewrite bte_sym in H1.
rewrite bte_sym in H2.
apply btm_congr_l with (1 := H1), btm_congr_r with (1 := H2); auto.
Tactic Notation "btm" "simpl" := repeat match goal with | |- context[_ ∈ _ ⪧ _] => rewrite btm_inv; auto; try tauto | |- context[_ ∈ ∅] => rewrite btm_inv_0; auto; try tauto end.
Section bte_depth.
Opaque max.
Fact bte_depth_eq s t : s ≈ t -> ⌞s⌟ = ⌞t⌟.
Proof.
induction 1; simpl; auto.
+
transitivity ⌞s⌟; auto.
+
rewrite max_assoc, max_idempotent; auto.
+
rewrite max_assoc, (max_comm (S _)), max_assoc; auto.
Fact btm_depth s t : s ∈ t -> ⌞s⌟ < ⌞t⌟.
Proof.
intros H; apply bte_depth_eq in H.
rewrite <- H; simpl.
apply lt_le_trans with (1 := lt_n_Sn _).
apply le_max_l.
End bte_depth.
Definition btree_wf_rect := well_founded_induction_type btm_wf.
Section establishing_decidability.
Reserved Notation "x ≺ y" (at level 70, no associativity).
Inductive bt_lt : bt -> bt -> Prop := | in_btlt_0 : forall s t, ∅ ≺ s⪧t | in_btlt_1 : forall s s' t t', s ≺ s' -> s⪧t ≺ s'⪧t' | in_btlt_2 : forall s t t', t ≺ t' -> s⪧t ≺ s⪧t' where "s ≺ t" := (bt_lt s t).
Hint Constructors bt_lt : core.
Fact bt_lt_irrefl s : ~ s ≺ s.
Proof.
intros H.
assert (forall t, s ≺ t -> s <> t) as D; [ | apply D in H; destruct H; auto ].
clear H; induction 1 as [ s t | s s' t t' H IH | s t t' H IH ]; try discriminate; contradict IH; inversion IH; auto.
Fact bt_lt_trans r s t : r ≺ s -> s ≺ t -> r ≺ t.
Proof.
intros H1; revert H1 t.
induction 1; inversion 1; auto.
Fact bt_lt_eq_lt_dec s t : { s ≺ t } + { s = t } + { t ≺ s }.
Proof.
revert t; induction s as [ | s1 H1 s2 H2 ] using bt_rect; intros [ | t1 t2 ]; auto.
destruct (H1 t1) as [ [] | ]; auto; destruct (H2 t2) as [ [] | ]; subst; auto.
Fixpoint bt_insert s t : bt := match t with | ∅ => s⪧∅ | t⪧u => match bt_lt_eq_lt_dec s t with | inleft (left _) => s⪧t⪧u | inleft (right _) => t⪧u | inright _ => t⪧(s→u) end end where "s → t" := (bt_insert s t).
Fact bt_lt_eq_lt_dec_refl s : exists H, bt_lt_eq_lt_dec s s = inleft (right H).
Proof.
destruct (bt_lt_eq_lt_dec s s) as [ [ C | H ] | C ].
1,3: exfalso; revert C; apply bt_lt_irrefl.
exists H; auto.
Ltac bt_lt_eq H := match goal with |- context [bt_lt_eq_lt_dec ?x ?x] => destruct (bt_lt_eq_lt_dec_refl x) as (H & ->) end.
Fact bt_insert_leaf s : s→∅ = s⪧∅.
Proof.
reflexivity.
Fact bt_insert_eq s t : s→s⪧t = s⪧t.
Proof.
simpl; bt_lt_eq H; auto.
Fact bt_insert_lt s t u : s ≺ t -> s→t⪧u = s⪧t⪧u.
Proof.
intros H; simpl.
destruct (bt_lt_eq_lt_dec s t) as [[|]|]; auto.
+
contradict H; subst; apply bt_lt_irrefl.
+
destruct (@bt_lt_irrefl s); apply bt_lt_trans with t; auto.
Fact bt_insert_gt s t u : t ≺ s -> s→t⪧u = t⪧(s→u).
Proof.
intros H; simpl.
destruct (bt_lt_eq_lt_dec s t) as [[|]|]; auto.
+
destruct (@bt_lt_irrefl s); apply bt_lt_trans with t; auto.
+
contradict H; subst; apply bt_lt_irrefl.
Fact bt_insert_equiv s t : s→t ≈ s⪧t.
Proof.
induction t as [ | t u Hu ] using bt_rect'; simpl; auto.
destruct (bt_lt_eq_lt_dec s t) as [[]|]; subst; auto.
apply bte_trans with (t⪧s⪧u); auto.
Fixpoint bt_norm t := match t with | ∅ => ∅ | s⪧t => s† → t† end where "t †" := (bt_norm t).
Hint Resolve bt_insert_equiv : core.
Fact bt_norm_eq t : t† ≈ t.
Proof.
induction t as [ | s ? t ? ]; simpl; auto.
apply bte_trans with (s†⪧t†); auto.
Opaque bt_insert.
Tactic Notation "rew" "bt" "insert" := repeat match goal with | |- context[_→∅] => rewrite bt_insert_leaf | |- context[?x→?x⪧_] => rewrite bt_insert_eq | H : ?x ≺ ?y |- context[?x→?y⪧_] => rewrite bt_insert_lt with (1 := H) | H : ?x ≺ ?y |- context[?y→?x⪧_] => rewrite bt_insert_gt with (1 := H) end.
Tactic Notation "bt" "insert" "case" hyp(x) hyp(y) := destruct (bt_lt_eq_lt_dec x y) as [ [|] | ]; subst; rew bt insert; auto.
Tactic Notation "bt" "lt" "trans" constr(t) := apply bt_lt_trans with t; auto.
Tactic Notation "bt" "lt" "cycle" := match goal with | H1 : ?x ≺ ?x |- _ => destruct (@bt_lt_irrefl x); auto | H1 : ?x ≺ ?y, H2 : ?y ≺ ?x |- _ => destruct (@bt_lt_irrefl x); bt lt trans y | H1 : ?x ≺ ?y, H2 : ?y ≺ ?z, H3 : ?z ≺ ?x |- _ => destruct (@bt_lt_irrefl x); bt lt trans y; bt lt trans z end.
Fact bt_insert_cntr s t : s→s→t = s→t.
Proof.
induction t as [ | t1 t2 IH2 ] using bt_rect'; rew bt insert; auto.
bt insert case s t1; f_equal; auto.
Fact bt_insert_comm s t u : s→t→u = t→s→u.
Proof.
induction u as [ | u1 u2 IH ] using bt_rect'.
+
rew bt insert; bt insert case s t.
+
bt insert case t u1; bt insert case s u1; bt insert case s t; try bt lt cycle; f_equal; auto.
Hint Resolve bt_insert_cntr bt_insert_comm bt_norm_eq : core.
End establishing_decidability.
Section more_decidability.
Section btm_ex_dec.
Variable (P : bt -> Prop) (HP : forall s t, s ≈ t -> P s -> P t).
End btm_ex_dec.
Definition btm_select (P : _ -> Prop) t : (forall s t, s ≈ t -> P s -> P t) -> (forall x, x ∈ t -> { P x } + { ~ P x }) -> { s | forall x, x ∈ s <-> x ∈ t /\ P x }.
Proof.
intros HP0.
induction t as [ | s t Ht ] using bt_rect'; intros HP.
+
exists ∅; intros s; btm simpl.
+
destruct Ht as (t' & H').
*
intros x Hx; apply HP; btm simpl.
*
destruct (HP s) as [ H | H ]; btm simpl; auto.
-
exists (s⪧t'); intros x; btm simpl.
rewrite H'.
split; try tauto.
intros [ H1 | (H1 & H2) ]; auto.
split; auto.
revert H; apply HP0; auto.
-
exists t'; intros x; rewrite H'; btm simpl.
split; try tauto.
intros ([H1|H1] & H2); split; auto.
contradict H; revert H2; apply HP0; auto.
Definition btm_partition x s : x ∈ s -> { t | s ≈ x⪧t /\ x ∉ t }.
Proof.
induction s as [ | y s IHs ] using bt_rect'.
+
intros H; exfalso; revert H; btm simpl.
+
intros H; rewrite btm_inv in H.
destruct (bte_dec x y) as [ H1 | H1 ]; destruct (btm_dec x s) as [ H2 | H2 ]; try (exfalso; tauto).
*
destruct (IHs H2) as (t & H3 & H4).
exists t; split; auto.
rewrite <- H1, H3; auto.
*
exists s; auto.
*
destruct (IHs H2) as (t & H3 & H4).
exists (y⪧t); split; auto.
-
apply bte_trans with (y⪧x⪧t); auto.
-
contradict H4; revert H4; btm simpl.
End more_decidability.
Definition bt_incl x y := forall u, u ∈ x -> u ∈ y.
Local Infix "⊆" := bt_incl.
Add Parametric Morphism: (bt_incl) with signature (bt_equiv) ==> (bt_equiv) ==> (iff) as bti_congr.
Proof.
intros x y H1 a b H2; split; intros H z.
+
rewrite <- H2, <- H1; apply H.
+
rewrite H1, H2; apply H.
Fact bti_refl x : x ⊆ x.
Proof.
red; auto.
Hint Resolve bti_refl : core.
Fact bti_trans x y z : x ⊆ y -> y ⊆ z -> x ⊆ z.
Proof.
intros H1 H2 k Hx; apply H2, H1; auto.
Fact bti_comp s t : t ⊆ s⪧t.
Proof.
intro; rewrite btm_inv; auto.
Fact bti_0 x : ∅ ⊆ x.
Proof.
intro; btm simpl.
Fact bti_inv_0 x : x ⊆ ∅ <-> x = ∅.
Proof.
split; intros H; subst; auto.
destruct x as [ | s t ]; auto.
specialize (H s); revert H; btm simpl.
intros []; auto.
Fact bti_mono_r x s t : s ⊆ t -> x⪧s ⊆ x⪧t.
Proof.
intros ? ?; btm simpl; intros []; auto.
Fact bte_bti s t : s ≈ t -> s ⊆ t.
Proof.
intros ? ?; apply btm_congr_r; auto.
Fact btm_bti x s : x ∈ s -> x⪧s ⊆ s.
Proof.
intro; apply bte_bti; auto.
Fact bti_congr_l x y t : x ≈ y -> x ⊆ t-> y ⊆ t.
Proof.
intros H1 H2 z Hz.
apply H2; revert Hz; apply btm_congr_r; auto.
Fact bti_congr_r x s t : s ≈ t -> x ⊆ s -> x ⊆ t.
Proof.
intros H1 H2 z Hz.
generalize (H2 _ Hz); apply btm_congr_r; auto.
Hint Resolve bti_0 bti_refl bti_comp bti_mono_r : core.
Fact bte_incl_equiv s t : s ≈ t <-> s ⊆ t /\ t ⊆ s.
Proof.
split.
+
intro; split; apply bte_bti; auto.
+
intros []; apply bti_equiv; auto.
Fact bte_ext s t : s ≈ t <-> forall x, x ∈ s <-> x ∈ t.
Proof.
rewrite bte_incl_equiv; firstorder.
Fact bti_inv x s t : x ⊆ s⪧t <-> x ⊆ t \/ exists y, y ⊆ t /\ x ≈ s⪧y.
Proof.
split.
+
intros H.
destruct (btm_dec s x) as [ H1 | H1 ].
*
destruct btm_partition with (1 := H1) as (y & H2 & H3).
right; exists y; split; auto.
intros z Hz.
assert (z ∈ s⪧t) as C.
{
apply H.
apply btm_congr_r with (1 := in_bte_sym H2), btm_inv; auto.
}
apply btm_inv in C; destruct C as [C|]; auto.
contradict H3; revert Hz; apply btm_congr_l; auto.
*
left.
intros y Hy.
specialize (H _ Hy).
apply btm_inv in H.
destruct H as [ H | ]; auto.
contradict H1.
revert Hy; apply btm_congr_l; auto.
+
intros [ H | (y & H1 & H2) ].
*
apply bti_trans with (1 := H); auto.
*
intros z Hz.
apply bti_congr_r with (1 := H2) in Hz; auto.
revert Hz; btm simpl; intros []; auto.
Fixpoint bt_cup s t := match s with | ∅ => t | x⪧s => x⪧(s ∪ t) end where "s ∪ t" := (bt_cup s t).
Fact bt_cup_left s t : s ⊆ s ∪ t.
Proof.
intro; rewrite bt_cup_spec; auto.
Fact bt_cup_right s t : t ⊆ s ∪ t.
Proof.
intro; rewrite bt_cup_spec; auto.
Hint Resolve bt_cup_left bt_cup_right : core.
Add Parametric Morphism: (bt_cup) with signature (bt_equiv) ==> (bt_equiv) ==> (bt_equiv) as bt_cup_congr.
Proof.
intros s s' H t t'; revert H.
do 3 rewrite bte_ext; intros H1 H2 x.
do 2 rewrite bt_cup_spec.
rewrite H1, H2; tauto.
Fact bt_cup_incl s t x : s ∪ t ⊆ x <-> s ⊆ x /\ t ⊆ x.
Proof.
split.
+
intros H; split; apply bti_trans with (2 := H); auto.
+
intros [] z; rewrite bt_cup_spec; intros []; auto.
Fact bt_cup_mono s s' t t' : s ⊆ s' -> t ⊆ t' -> s ∪ t ⊆ s' ∪ t'.
Proof.
intros H1 H2 x; do 2 rewrite bt_cup_spec.
intros [ H | H ]; [ left | right ]; revert H; auto.
Hint Resolve bt_cup_mono : core.
Definition bt_transitive t := forall u v, u ∈ v -> v ∈ t -> u ∈ t.
Fact bt_transitive_incl u t : bt_transitive t -> u ∈ t -> u ⊆ t.
Proof.
intros H H1 x H2.
revert H2 H1; apply H.
Fixpoint bt_tc t := match t with | ∅ => ∅ | s⪧t => s⪧(↓s ∪ ↓t) end where "↓ t" := (bt_tc t).
Fact bt_tc_incr t : t ⊆ ↓t.
Proof.
intro; induction t; simpl; auto; btm simpl.
rewrite bt_cup_spec; tauto.
Hint Resolve bt_tc_incr : core.
Hint Resolve bt_tc_trans : core.
Fact bt_tc_incl_transitive s t : bt_transitive t -> s ⊆ t -> ↓s ⊆ t.
Proof.
intros H.
induction s as [ | u Hu v Hv ]; simpl; auto.
intros H1 x; btm simpl; rewrite bt_cup_spec.
intros [ H2 | [ H2 | H2 ] ].
+
rewrite H2; apply H1; btm simpl.
+
revert H2; apply Hu.
intros a Ha; apply H with (1 := Ha), H1; btm simpl.
+
revert H2; apply Hv; intros ? ?; apply H1; btm simpl.
Fact bt_tc_mono s t : s ⊆ t -> ↓s ⊆ ↓t.
Proof.
intros H.
apply bt_tc_incl_transitive; auto.
apply bti_trans with (1 := H); auto.
Fact bt_tc_idem t : (↓↓t) ⊆ ↓t.
Proof.
apply bt_tc_incl_transitive; auto.
Hint Resolve bt_tc_mono bt_tc_idem : core.
Fact bt_tc_cup s t : ↓(s ∪ t) ⊆ ↓s ∪ ↓t.
Proof.
apply bt_tc_incl_transitive; auto.
intros x y; do 2 rewrite bt_cup_spec.
intros H [ H1 | H1 ]; [ left | right ]; revert H H1; apply bt_tc_trans.
Fact bt_tc_congr_l u v t : u ≈ v -> u ∈ ↓t -> v ∈ ↓t.
Proof.
revert u v; induction t using bt_rect'; simpl; intros ? ? ?; apply btm_congr_l; auto.
Fact bt_tc_congr_r u s t : s ≈ t -> u ∈ ↓s <-> u ∈ ↓t.
Proof.
intros H; revert u.
rewrite bte_incl_equiv in H; destruct H.
apply bte_ext, bti_equiv; auto.
Add Parametric Morphism: (bt_tc) with signature (bt_equiv) ==> (bt_equiv) as bt_tc_congr.
Proof.
intros; apply bte_ext; intro; apply bt_tc_congr_r; auto.
Section bt_pow.
Fixpoint bt_mcomp x t := match t with | ∅ => ∅ | s⪧t => (x⪧s) ⪧ (bt_mcomp x t) end.
Fact bt_mcomp_spec x t u : u ∈ bt_mcomp x t <-> exists k, k ∈ t /\ u ≈ x⪧k.
Proof.
revert u; induction t as [ | s t Ht ] using bt_rect'; intros u; simpl.
+
rewrite btm_inv_0; split; try tauto.
intros (k & Hk & _); revert Hk; rewrite btm_inv_0; auto.
+
rewrite btm_inv; split.
*
intros [ H | H ].
-
exists s; split; auto; btm simpl.
-
rewrite Ht in H.
destruct H as (k & ? & ?).
exists k; split; auto.
btm simpl.
*
intros (k & H1 & H2); revert H1 H2.
rewrite btm_inv, Ht.
intros [H2|H2] H1; auto.
-
left; apply bte_trans with (1 := H1); auto.
-
right; exists k; auto.
Fixpoint bt_pow t := match t with | ∅ => ∅⪧∅ | x⪧t => bt_pow t ∪ bt_mcomp x (bt_pow t) end.
Fact bt_pow_spec t x : x ∈ bt_pow t <-> x ⊆ t.
Proof.
revert x; induction t as [ | s t Ht ] using bt_rect'; intros x; simpl.
+
rewrite btm_inv, btm_inv_0, bti_inv_0, bte_inv_0; tauto.
+
rewrite bti_inv, bt_cup_spec, bt_mcomp_spec, Ht.
split; intros [ | (y & H) ]; auto; right; exists y; revert H; rewrite Ht; auto.
Fact bt_pow_transitive t : bt_transitive t -> bt_transitive (bt_pow t).
Proof.
intros H x y H1.
do 2 rewrite bt_pow_spec.
intros H2 z Hz.
apply H2 in H1.
revert Hz H1; apply H.
Fact bt_pow_trans_incl t : bt_transitive t -> t ⊆ bt_pow t.
Proof.
intros Ht.
intros x Hx.
apply bt_pow_spec; intros y Hy.
revert Hx; apply Ht; auto.
Fact bt_pow_iter_trans t n : bt_transitive t -> bt_transitive (iter bt_pow t n) /\ t ⊆ iter bt_pow t n.
Proof.
revert t; induction n as [ | n IHn ]; simpl; intros t Ht; auto; split.
+
apply IHn, bt_pow_transitive; auto.
+
destruct (IHn _ (bt_pow_transitive Ht)) as [ _ H ].
apply bti_trans with (2 := H), bt_pow_trans_incl; auto.
Fact bt_pow_iter_mono t t' n : t ⊆ t' -> iter bt_pow t n ⊆ iter bt_pow t' n.
Proof.
revert t t'; induction n as [ | n IHn ]; simpl; auto; intros t t' H.
apply IHn; intro; do 2 rewrite bt_pow_spec.
intro; apply bti_trans with t; auto.
Fact bt_pow_iter_le t n m : n <= m -> bt_transitive t -> iter bt_pow t n ⊆ iter bt_pow t m.
Proof.
intros H; revert H t.
induction 1 as [ | m Hm IHm ]; auto; intros t Ht.
apply bti_trans with (1 := IHm _ Ht); simpl.
apply bt_pow_iter_mono, bt_pow_trans_incl; auto.
End bt_pow.
Add Parametric Morphism: (bt_pow) with signature (bt_equiv) ==> (bt_equiv) as bt_pow_congr.
Proof.
intros ? ? H; apply bte_ext; intro; do 2 rewrite bt_pow_spec; rewrite H; tauto.
Definition bt_opair s t := (s⪧∅)⪧(s⪧t⪧∅)⪧∅.
Local Notation "⟬ s , t ⟭" := (bt_opair s t).
Section ordered_pairs.
Fact bt_sg_inv x y : x⪧∅ ≈ y⪧∅ <-> x ≈ y.
Proof.
split; auto.
rewrite bte_ext.
intros H; specialize (H x).
do 2 rewrite btm_inv, btm_inv_0 in H.
apply proj1 in H; destruct H; try tauto; auto.
Fact bt_sg_db_inv a x y : a⪧∅ ≈ x⪧y⪧∅ <-> a ≈ x /\ a ≈ y.
Proof.
split.
+
intros H.
rewrite bte_ext in H.
generalize (proj2 (H x)) (proj2 (H y)).
btm simpl; intros [|[]] [|[]]; auto.
+
intros [].
apply bte_trans with (a⪧a⪧∅); auto.
Fact bt_db_inv a b x y : a⪧b⪧∅ ≈ x⪧y⪧∅ <-> a ≈ x /\ b ≈ x /\ x ≈ y \/ a ≈ x /\ b ≈ y \/ a ≈ y /\ b ≈ x.
Proof.
split.
+
intros H.
rewrite bte_ext in H.
generalize (proj1 (H a)) (proj1 (H b)) (proj2 (H x)) (proj2 (H y)).
btm simpl; intros [|[|[]]] [|[|[]]] [|[|[]]] [|[|[]]]; auto.
+
intros [ (H1&H2&H3) | [ (H1&H2) | (H1&H2) ] ]; auto.
*
do 2 (apply in_bte_cngr; auto).
apply bte_trans with x; auto.
*
apply bte_trans with (1 := in_bte_comm _ _ _).
do 2 (apply in_bte_cngr; auto).
Fact bt_opair_spec x s t : x ∈ ⟬s,t⟭ <-> x ≈ s⪧∅ \/ x ≈ s⪧t⪧∅.
Proof.
unfold bt_opair; btm simpl.
Fact bt_opair_equiv s t s' t' : ⟬s,t⟭ ≈⟬s',t'⟭ <-> s≈s' /\ t≈t'.
Proof.
split.
2: intros []; unfold bt_opair; auto.
intros H; rewrite bte_ext in H.
assert (forall x, (x ≈ s⪧∅ \/ x ≈ s⪧t⪧∅) <-> (x ≈ s'⪧∅ \/ x ≈ s'⪧t'⪧∅)) as H'.
{
intros x; generalize (H x); do 2 rewrite bt_opair_spec; tauto.
}
clear H; revert H'; intros H.
generalize (proj1 (H _) (or_introl (in_bte_refl _))) (proj1 (H _) (or_intror (in_bte_refl _))) (proj2 (H _) (or_introl (in_bte_refl _))) (proj2 (H _) (or_intror (in_bte_refl _))).
repeat rewrite bt_db_inv.
do 2 rewrite (bte_sym (_⪧_⪧_)).
repeat rewrite bt_sg_inv.
repeat rewrite bt_sg_db_inv.
intros.
repeat match goal with | H : _ /\ _ |- _ => destruct H | H : _ \/ _ |- _ => destruct H end; split; auto; try (apply bte_trans with s); auto; try (apply bte_trans with s'); auto.
End ordered_pairs.
Add Parametric Morphism: (bt_opair) with signature (bt_equiv) ==> (bt_equiv) ==> (bt_equiv) as bt_pair_congr.
Proof.
intros; apply bt_opair_equiv; auto.
Fact btm_opair_pow x y t : x ∈ t -> y ∈ t -> ⟬x,y⟭ ∈ bt_pow (bt_pow t).
Proof.
rewrite bt_pow_spec.
intros Hx Hy p.
rewrite bt_opair_spec.
intros [H|H]; apply bte_sym in H; apply btm_congr_l with (1 := H); apply bt_pow_spec.
+
intros z; btm simpl; intros [ Hz | [] ].
revert Hx; apply btm_congr_l; auto.
+
intros z; btm simpl; intros [ Hz | [ Hz | [] ] ]; [ revert Hx | revert Hy ]; apply btm_congr_l; auto.
Section FOL_encoding.
Fact bt_enc_equiv s t : s ≈ t <-> forall x, x ∈ s <-> x ∈ t.
Proof.
apply bte_ext.
Fact bt_enc_empty s : s ≈ ∅ <-> forall x, ~ x ∈ s.
Proof.
rewrite bte_ext; apply forall_equiv; intro; btm simpl.
Fact bt_enc_sg s t : s ≈ t⪧∅ <-> forall x, x ∈ s <-> x ≈ t.
Proof.
rewrite bte_ext; apply forall_equiv; intro; btm simpl.
Fact bt_enc_db u s t : u ≈ s⪧t⪧∅ <-> forall x, x ∈ u <-> x ≈ s \/ x ≈ t.
Proof.
rewrite bte_ext; apply forall_equiv; intros; btm simpl.
Fact bt_enc_opair p s t : p ≈ ⟬s,t⟭ <-> (forall x, x ∈ p <-> x ≈ s⪧∅ \/ x ≈ s⪧t⪧∅).
Proof.
rewrite bte_ext; apply forall_equiv; intro.
rewrite bt_opair_spec; tauto.
Fact bt_enc_otriple p r s t : p ≈ ⟬r,⟬s,t⟭⟭ <-> exists a, p ≈ ⟬r,a⟭ /\ a ≈ ⟬s,t⟭ .
Proof.
split.
+
exists ⟬s,t⟭; auto.
+
intros (a & H1 & H2).
apply bte_trans with (1 := H1).
apply bt_opair_equiv; auto.
Fact bt_enc_rel3 a b c t : ⟬a,⟬b,c⟭⟭ ∈ t <-> exists p, p ≈ ⟬a,⟬b,c⟭⟭ /\ p ∈ t.
Proof.
split.
+
exists ⟬a,⟬b,c⟭⟭ ; auto.
+
intros (p & H1 & H2).
revert H2; apply btm_congr_l; auto.
Fixpoint tuple (l : list bt) := match l with | nil => ∅ | x::l => ⟬x,tuple l⟭ end.
Fact bt_enc_tuple_0 p : p ≈ tuple nil <-> p ≈ ∅.
Proof.
simpl; tauto.
Fact bt_enc_tuple p x l : p ≈ tuple (x::l) <-> exists a, p ≈ ⟬x,a⟭ /\ a ≈ tuple l.
Proof.
simpl; split.
+
exists (tuple l); auto; split; auto.
+
intros (a & H1 & H2).
apply bte_trans with (1 := H1).
apply bt_opair_equiv; auto.
End FOL_encoding.
Section nat2bt.
Fixpoint nat2bt n : bt := match n with | 0 => ∅ | S n => (nat2bt n)⪧(nat2bt n) end.
Fact nat2bt_transitive n : bt_transitive (nat2bt n).
Proof.
induction n as [ | n IHn ]; simpl.
+
intros ? ?; btm simpl.
+
intros a b; btm simpl.
intros H1 [ H2 | H3 ]; right.
*
rewrite <- H2; auto.
*
revert H1 H3; apply IHn.
Hint Resolve nat2bt_transitive : core.
Fact nat2bt_mono n m : n <= m -> nat2bt n ⊆ nat2bt m.
Proof.
induction 1 as [ | m Hm IHm ]; auto.
apply bti_trans with (1 := IHm).
apply bt_transitive_incl; auto.
simpl; btm simpl.
Let nat2bt_inv_full m x : x ∈ nat2bt m -> { n | n < m /\ x ≈ nat2bt n }.
Proof.
revert x; induction m as [ | m IHm ]; intros x; simpl; btm simpl.
+
intro E; exfalso; revert E; btm simpl.
+
intros H; rewrite btm_inv in H.
destruct (bte_dec x (nat2bt m)) as [ H1 | H1 ].
*
exists m; split; auto.
*
destruct (IHm x) as (n & H2 & H3); try tauto.
exists n; split; auto; lia.
Definition bt2nat n x Hx := proj1_sig (@nat2bt_inv_full n x Hx).
Fact bt2nat_lt n x Hx : @bt2nat n x Hx < n.
Proof.
apply (proj2_sig (@nat2bt_inv_full n x Hx)).
Fact bt2nat_fix n x Hx : nat2bt (@bt2nat n x Hx) ≈ x.
Proof.
apply bte_sym, (proj2_sig (@nat2bt_inv_full n x Hx)).
Fact nat2bt_inj n m : nat2bt n ≈ nat2bt m -> n = m.
Proof.
revert m; induction n as [ | n IHn ]; intros [ | m ]; simpl; auto.
+
intros H; symmetry in H; apply bte_discr in H; tauto.
+
intros H; apply bte_discr in H; tauto.
+
intros H; rewrite bte_ext in H.
f_equal; apply IHn; clear IHn.
generalize (proj1 (H (nat2bt n))) (proj2 (H (nat2bt m))); btm simpl.
intros [H0 | H0] [H1 | H1]; auto.
apply btm_depth in H0.
apply btm_depth in H1.
lia.
Hint Resolve nat2bt_mono : core.
Fact nat2bt_order_iso n m : nat2bt n ⊆ nat2bt m <-> n <= m.
Proof.
split; eauto.
intros H.
destruct (le_lt_dec m n); try lia.
cut (n = m); try lia.
apply nat2bt_inj, bti_equiv; eauto.
Fact nat2bt_strict n m : nat2bt n ∈ nat2bt m <-> n < m.
Proof.
split.
+
intros H.
destruct (le_lt_dec m n) as [ H1 | ]; auto.
generalize (nat2bt_mono H1 H); intros H2.
apply btm_depth in H2; lia.
+
intros H; apply (nat2bt_mono H).
simpl; btm simpl.
End nat2bt.
Section pos2bt.
Definition pos2bt n (p : pos n) := nat2bt (pos2nat p).
Fact pos2bt_in n p : @pos2bt n p ∈ nat2bt n.
Proof.
apply nat2bt_strict, pos2nat_prop.
Let bt2pos_full n x : x ∈ nat2bt n -> { p | x ≈ @pos2bt n p }.
Proof.
intros Hx.
assert (bt2nat _ Hx < n).
{
apply nat2bt_strict; rewrite bt2nat_fix; auto.
}
exists (nat2pos H); unfold pos2bt; rewrite pos2nat_nat2pos.
rewrite bt2nat_fix; auto.
Definition bt2pos n x Hx := proj1_sig (@bt2pos_full n x Hx).
Fact bt2pos_fix n x Hx : pos2bt (@bt2pos n x Hx) ≈ x.
Proof.
apply bte_sym, (proj2_sig (@bt2pos_full n x Hx)).
Fact pos2bt_inj n p q : @pos2bt n p ≈ pos2bt q -> p = q.
Proof.
intro H; apply pos2nat_inj, nat2bt_inj, H.
End pos2bt.

Theorem btm_ex_dec t : (forall x, x ∈ t -> { P x } + { ~ P x }) -> { s | s ∈ t /\ P s } + { forall s, s ∈ t -> ~ P s }.
Proof.
induction t as [ | s t IHt ] using bt_rect'; intros Ht.
+
right; intros ?; btm simpl.
+
destruct (Ht s) as [ H | H ]; btm simpl; auto.
*
left; exists s; btm simpl; auto.
*
destruct IHt as [ (x & H1 & H2) | H1 ].
-
intros x Hx; apply Ht; btm simpl.
-
left; exists x; btm simpl.
-
right; intros x; btm simpl.
intros [ | ]; auto.
Admitted.

Corollary btm_fa_dec (P : _ -> Prop) t : (forall s t, s ≈ t -> P s -> P t) -> (forall x, x ∈ t -> { P x } + { ~ P x }) -> { s | s ∈ t /\ ~ P s } + { forall s, s ∈ t -> P s }.
Proof.
intros H1 H2.
destruct btm_ex_dec with (P := fun x => ~ P x) (t := t) as [ H | H ]; auto.
+
intros u v G1 G2; contradict G2; revert G2; apply H1; auto.
+
intros x Hx; specialize (H2 _ Hx); tauto.
+
right; intros s Hs; specialize (H _ Hs).
Admitted.

Definition btm_select (P : _ -> Prop) t : (forall s t, s ≈ t -> P s -> P t) -> (forall x, x ∈ t -> { P x } + { ~ P x }) -> { s | forall x, x ∈ s <-> x ∈ t /\ P x }.
Proof.
intros HP0.
induction t as [ | s t Ht ] using bt_rect'; intros HP.
+
exists ∅; intros s; btm simpl.
+
destruct Ht as (t' & H').
*
intros x Hx; apply HP; btm simpl.
*
destruct (HP s) as [ H | H ]; btm simpl; auto.
-
exists (s⪧t'); intros x; btm simpl.
rewrite H'.
split; try tauto.
intros [ H1 | (H1 & H2) ]; auto.
split; auto.
revert H; apply HP0; auto.
-
exists t'; intros x; rewrite H'; btm simpl.
split; try tauto.
intros ([H1|H1] & H2); split; auto.
Admitted.

Definition btm_partition x s : x ∈ s -> { t | s ≈ x⪧t /\ x ∉ t }.
Proof.
induction s as [ | y s IHs ] using bt_rect'.
+
intros H; exfalso; revert H; btm simpl.
+
intros H; rewrite btm_inv in H.
destruct (bte_dec x y) as [ H1 | H1 ]; destruct (btm_dec x s) as [ H2 | H2 ]; try (exfalso; tauto).
*
destruct (IHs H2) as (t & H3 & H4).
exists t; split; auto.
rewrite <- H1, H3; auto.
*
exists s; auto.
*
destruct (IHs H2) as (t & H3 & H4).
exists (y⪧t); split; auto.
-
apply bte_trans with (y⪧x⪧t); auto.
-
Admitted.

Fact bti_refl x : x ⊆ x.
Proof.
Admitted.

Fact bti_trans x y z : x ⊆ y -> y ⊆ z -> x ⊆ z.
Proof.
Admitted.

Fact bti_comp s t : t ⊆ s⪧t.
Proof.
Admitted.

Fact bti_0 x : ∅ ⊆ x.
Proof.
Admitted.

Fact bti_inv_0 x : x ⊆ ∅ <-> x = ∅.
Proof.
split; intros H; subst; auto.
destruct x as [ | s t ]; auto.
specialize (H s); revert H; btm simpl.
Admitted.

Fact bti_mono_r x s t : s ⊆ t -> x⪧s ⊆ x⪧t.
Proof.
Admitted.

Fact btm_bti x s : x ∈ s -> x⪧s ⊆ s.
Proof.
Admitted.

Fact bti_congr_l x y t : x ≈ y -> x ⊆ t-> y ⊆ t.
Proof.
intros H1 H2 z Hz.
Admitted.

Fact bti_congr_r x s t : s ≈ t -> x ⊆ s -> x ⊆ t.
Proof.
intros H1 H2 z Hz.
Admitted.

Lemma bti_dec s t : { s ⊆ t } + { ~ s ⊆ t }.
Proof.
destruct btm_fa_dec with (P := fun x => x ∈ t) (t := s) as [ (x & H1 & H2) | H1 ]; auto.
+
intros ? ?; apply btm_congr_l.
+
Admitted.

Lemma bti_equiv s t : s ⊆ t -> t ⊆ s -> s ≈ t.
Proof.
revert t; induction s as [ | x s Hs ] using bt_rect'.
+
intros t _ Ht.
destruct t as [ | y t ]; auto.
generalize (Ht y); btm simpl.
intros []; auto.
+
induction t as [ | y _ t Ht ].
*
intros H _; generalize (H x).
btm simpl; intros []; auto.
*
intros H1 H2.
destruct (btm_dec x s) as [ H3 | H3 ].
-
apply bte_trans with s; auto.
apply Hs.
++
apply bti_trans with (2 := H1); auto.
++
apply bti_trans with (1 := H2), btm_bti; auto.
-
assert (x ∈ y⪧t) as H4 by (apply H1; auto; btm simpl).
destruct btm_partition with (1 := H4) as (u & H5 & H6).
assert (s ≈ u) as H7.
{
apply Hs.
+
intros z Hz.
assert (z ∈ x⪧u) as H7.
{
apply btm_congr_r with (1 := H5), H1, btm_inv; auto.
}
apply btm_inv in H7; destruct H7 as [ H7 | ]; auto.
contradict H3; revert Hz; apply btm_congr_l; auto.
+
intros z Hz.
assert (z ∈ x⪧s) as H7.
{
apply H2, btm_congr_r with (1 := in_bte_sym H5), btm_inv; auto.
}
apply btm_inv in H7; destruct H7 as [ H7 | ]; auto.
contradict H6; revert Hz; apply btm_congr_l; auto.
}
Admitted.

Fact bte_incl_equiv s t : s ≈ t <-> s ⊆ t /\ t ⊆ s.
Proof.
split.
+
intro; split; apply bte_bti; auto.
+
Admitted.

Fact bte_ext s t : s ≈ t <-> forall x, x ∈ s <-> x ∈ t.
Proof.
Admitted.

Fact bti_inv x s t : x ⊆ s⪧t <-> x ⊆ t \/ exists y, y ⊆ t /\ x ≈ s⪧y.
Proof.
split.
+
intros H.
destruct (btm_dec s x) as [ H1 | H1 ].
*
destruct btm_partition with (1 := H1) as (y & H2 & H3).
right; exists y; split; auto.
intros z Hz.
assert (z ∈ s⪧t) as C.
{
apply H.
apply btm_congr_r with (1 := in_bte_sym H2), btm_inv; auto.
}
apply btm_inv in C; destruct C as [C|]; auto.
contradict H3; revert Hz; apply btm_congr_l; auto.
*
left.
intros y Hy.
specialize (H _ Hy).
apply btm_inv in H.
destruct H as [ H | ]; auto.
contradict H1.
revert Hy; apply btm_congr_l; auto.
+
intros [ H | (y & H1 & H2) ].
*
apply bti_trans with (1 := H); auto.
*
intros z Hz.
apply bti_congr_r with (1 := H2) in Hz; auto.
Admitted.

Theorem bt_cup_spec x s t : x ∈ s ∪ t <-> x ∈ s \/ x ∈ t.
Proof.
revert x; induction s as [ | y s Hs ] using bt_rect'; intros x; simpl; btm simpl.
Admitted.

Fact bt_cup_left s t : s ⊆ s ∪ t.
Proof.
Admitted.

Fact bte_bti s t : s ≈ t -> s ⊆ t.
Proof.
intros ? ?; apply btm_congr_r; auto.
