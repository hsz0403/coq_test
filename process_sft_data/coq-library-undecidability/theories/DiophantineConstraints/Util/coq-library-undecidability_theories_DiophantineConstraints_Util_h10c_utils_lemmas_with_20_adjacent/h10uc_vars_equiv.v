Require Import List Arith.
From Undecidability.Shared.Libs.DLW.Utils Require Import utils_decidable utils_nat.
From Undecidability.DiophantineConstraints Require Import H10C.
Set Implicit Arguments.
Local Notation "〚 c 〛" := (h10c_sem c).
Local Notation " '⟪' c '⟫' " := (fun φ => h10uc_sem φ c).
Section decidability_of_validity.
Let plus_swap (P Q : Prop) : { P } + { Q } -> { Q } + { P }.
Proof.
tauto.
Fact h10c_sem_dec c φ : {〚c〛φ } + { ~〚c〛φ }.
Proof.
destruct c; apply eq_nat_dec.
Fact h10lc_sem_dec l φ : { c | In c l /\ ~〚c〛φ } + { forall c, In c l ->〚c〛φ }.
Proof.
apply list_choose_dep.
intros c _; apply plus_swap, h10c_sem_dec.
Fact h10luc_sem_dec l φ : { c | In c l /\ ~ ⟪c⟫ φ } + { forall c, In c l -> ⟪c⟫ φ }.
Proof.
apply list_choose_dep.
intros c _; apply plus_swap.
destruct c as ((?,?),?); apply eq_nat_dec.
End decidability_of_validity.
Section h10c_vars_bound.
Definition h10c_vars c := match c with | h10c_one x => x::nil | h10c_plus x y z => x::y::z::nil | h10c_mult x y z => x::y::z::nil end.
Definition h10uc_vars (c : h10uc) := match c with (x,y,z) => x::y::z::nil end.
Fact h10c_vars_equiv c phi psy : (forall x, In x (h10c_vars c) -> phi x = psy x) -> 〚c〛phi <->〚c〛psy.
Proof.
destruct c; simpl; intros H; repeat rewrite H; tauto.
Fact h10uc_vars_equiv c phi psy : (forall x, In x (h10uc_vars c) -> phi x = psy x) -> ⟪c⟫ phi <-> ⟪c⟫ psy.
Proof.
destruct c as ((?,?),?); simpl; intros H; repeat rewrite H; tauto.
Definition h10lc_vars := flat_map h10c_vars.
Definition h10luc_vars := flat_map h10uc_vars.
Fact h10lc_vars_equiv l phi psy : (forall x, In x (h10lc_vars l) -> phi x = psy x) -> forall c, In c l ->〚c〛phi <->〚c〛psy.
Proof.
intros H c Hc.
apply h10c_vars_equiv.
intros x Hx; apply H, in_flat_map.
exists c; auto.
Fact h10luc_vars_equiv l phi psy : (forall x, In x (h10luc_vars l) -> phi x = psy x) -> forall c, In c l -> ⟪c⟫ phi <-> ⟪c⟫ psy.
Proof.
intros H c Hc.
apply h10uc_vars_equiv.
intros x Hx; apply H, in_flat_map.
exists c; auto.
Definition h10lc_bound l := S (lmax (h10lc_vars l)).
Definition h10luc_bound l := S (lmax (h10luc_vars l)).
Fact h10lc_bound_prop l phi psy : (forall x, x < h10lc_bound l -> phi x = psy x) -> forall c, In c l ->〚c〛phi <->〚c〛psy.
Proof.
intros H; apply h10lc_vars_equiv.
intros x Hc; apply H, le_n_S, lmax_prop; auto.
Fact h10luc_bound_prop l phi psy : (forall x, x < h10luc_bound l -> phi x = psy x) -> forall c, In c l -> ⟪c⟫ phi <-> ⟪c⟫ psy.
Proof.
intros H; apply h10luc_vars_equiv.
intros x Hc; apply H, le_n_S, lmax_prop; auto.
End h10c_vars_bound.

Let plus_swap (P Q : Prop) : { P } + { Q } -> { Q } + { P }.
Proof.
Admitted.

Fact h10c_sem_dec c φ : {〚c〛φ } + { ~〚c〛φ }.
Proof.
Admitted.

Fact h10lc_sem_dec l φ : { c | In c l /\ ~〚c〛φ } + { forall c, In c l ->〚c〛φ }.
Proof.
apply list_choose_dep.
Admitted.

Fact h10luc_sem_dec l φ : { c | In c l /\ ~ ⟪c⟫ φ } + { forall c, In c l -> ⟪c⟫ φ }.
Proof.
apply list_choose_dep.
intros c _; apply plus_swap.
Admitted.

Fact h10c_vars_equiv c phi psy : (forall x, In x (h10c_vars c) -> phi x = psy x) -> 〚c〛phi <->〚c〛psy.
Proof.
Admitted.

Fact h10lc_vars_equiv l phi psy : (forall x, In x (h10lc_vars l) -> phi x = psy x) -> forall c, In c l ->〚c〛phi <->〚c〛psy.
Proof.
intros H c Hc.
apply h10c_vars_equiv.
intros x Hx; apply H, in_flat_map.
Admitted.

Fact h10luc_vars_equiv l phi psy : (forall x, In x (h10luc_vars l) -> phi x = psy x) -> forall c, In c l -> ⟪c⟫ phi <-> ⟪c⟫ psy.
Proof.
intros H c Hc.
apply h10uc_vars_equiv.
intros x Hx; apply H, in_flat_map.
Admitted.

Fact h10lc_bound_prop l phi psy : (forall x, x < h10lc_bound l -> phi x = psy x) -> forall c, In c l ->〚c〛phi <->〚c〛psy.
Proof.
intros H; apply h10lc_vars_equiv.
Admitted.

Fact h10luc_bound_prop l phi psy : (forall x, x < h10luc_bound l -> phi x = psy x) -> forall c, In c l -> ⟪c⟫ phi <-> ⟪c⟫ psy.
Proof.
intros H; apply h10luc_vars_equiv.
Admitted.

Fact h10uc_vars_equiv c phi psy : (forall x, In x (h10uc_vars c) -> phi x = psy x) -> ⟪c⟫ phi <-> ⟪c⟫ psy.
Proof.
destruct c as ((?,?),?); simpl; intros H; repeat rewrite H; tauto.
