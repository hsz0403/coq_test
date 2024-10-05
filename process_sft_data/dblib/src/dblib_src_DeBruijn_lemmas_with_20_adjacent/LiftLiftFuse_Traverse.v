Set Implicit Arguments.
Generalizable All Variables.
Require Import Arith.
Require Import Lia.
Require Import Dblib.DblibTactics.
Class Var (V : Type) := { var: nat -> V }.
Instance Var_idx : Var nat := { var x := x }.
Class Traverse (V T : Type) := { traverse: (nat -> nat -> V) -> (nat -> T -> T) }.
Notation traverse_var f := (traverse (fun l x => var (f l x))).
Class TraverseVarInjective `{Var V, Traverse V T} := { traverse_var_injective: forall f, (forall x1 x2 l, f l x1 = f l x2 -> x1 = x2) -> forall t1 t2 l, traverse_var f l t1 = traverse_var f l t2 -> t1 = t2 }.
Class TraverseFunctorial `{Traverse V V, Traverse V T} := { traverse_functorial: forall f g t l, traverse g l (traverse f l t) = traverse (fun l x => traverse g l (f l x)) l t }.
Class TraverseRelative `{Traverse V T} := { traverse_relative: forall f g p t m l, (forall l x, f (l + p) x = g l x) -> m = l + p -> traverse f m t = traverse g l t }.
Class TraverseIdentifiesVar `{Var V, Traverse V V} := { traverse_identifies_var: forall f l x, traverse f l (var x) = f l x }.
Class TraverseVarIsIdentity `{Var V, Traverse V T} := { traverse_var_is_identity: forall f, (forall l x, f l x = var x) -> forall t l, traverse f l t = t }.
Class Lift (T : Type) := { lift: nat -> nat -> T -> T }.
Instance Lift_idx : Lift nat := { lift w k x := if le_gt_dec k x then w + x else x }.
Notation shift := (lift 1).
Class Subst (V T : Type) := { subst: V -> nat -> T -> T }.
Definition subst_idx `{Var V} (v : V) (k x : nat) : V := match lt_eq_lt_dec x k with | inleft (left _) => var x | inleft (right _) => v | inright _ => var (x - 1) end.
Instance Subst_idx : Subst nat nat := { subst := subst_idx }.
Definition closed `{Lift T} k t := shift k t = t.
Definition rotate `{Var V, Lift T, Subst V T} (n : nat) (t : T) : T := subst (var n) 0 (shift (S n) t).
Class LiftVar `{Var A, Lift A} := { lift_var: forall w k x, lift w k (var x) = var (lift w k x) }.
Class LiftZero `{Lift T} := { lift_zero: forall k t, lift 0 k t = t }.
Class LiftInjective `{Lift T} := { lift_injective: forall w k t1 t2, lift w k t1 = lift w k t2 -> t1 = t2 }.
Ltac lift_injective := match goal with h: lift ?w ?k ?t1 = lift ?w ?k ?t2 |- _ => generalize (lift_injective _ _ _ _ h); clear h; intro h; try (subst t1) end.
Class LiftLift `{Lift T} := { lift_lift: forall t k s wk ws, k <= s -> lift wk k (lift ws s t) = lift ws (wk + s) (lift wk k t) }.
Class LiftLiftFuse `{Lift T} := { lift_lift_fuse: forall t k s wk ws, s <= k <= s + ws -> lift wk k (lift ws s t) = lift (wk + ws) s t }.
Class SubstVar `{Var A, Subst A A} := { subst_var: forall a k x, subst a k (var x) = subst_idx a k x }.
Class SubstLift `{Lift T, Subst V T} := { subst_lift: forall v k t, subst v k (shift k t) = t }.
Class LiftSubst1 `{Lift V, Lift T, Subst V T} := { lift_subst_1: forall t k v s w, k <= s -> lift w k (subst v s t) = subst (lift w k v) (w + s) (lift w k t) }.
Class LiftSubst2 `{Lift V, Lift T, Subst V T} := { lift_subst_2: forall t k v s w, s <= k -> lift w k (subst v s t) = subst (lift w k v) s (lift w (1 + k) t) }.
Class LiftSubst `{Lift V, Lift T, Subst V T} := { lift_subst: forall t k v s w, lift w k (subst v s t) = subst (lift w k v) (lift w (1 + k) s) (lift w (shift s k) t) }.
Class SubstSubst `{Lift V, Subst V V, Subst V T} := { subst_subst: forall t k v s w, k <= s -> subst v s (subst w k t) = subst (subst v s w) k (subst (shift k v) (1 + s) t) }.
Class Pun1 `{Var V, Lift T, Subst V T} := { pun_1: forall t k, subst (var k) (S k) (shift k t) = t }.
Class Pun2 `{Var V, Lift T, Subst V T} := { pun_2: forall t k, subst (var k) k (shift (S k) t) = t }.
Class PunPun `{Var V, Lift T, Subst V T} := { pun_pun: forall v w k t, subst v (w + k) (lift w k t) = subst v k (lift w (1 + k) t) }.
Class Rotate1SelfInverse `{Var V, Lift T, Subst V T} := { rotate1_self_inverse: forall t, rotate 1 (rotate 1 t) = t }.
Ltac just_do_it := unfold subst, Subst_idx, subst_idx, lift, Lift_idx, var, Var_idx; intros; dblib_by_cases; eauto with lia.
Create HintDb lift_idx_hints.
Ltac lift_idx := first [ rewrite @lift_idx_recent by solve [ lia | eauto with lift_idx_hints ] | rewrite @lift_idx_old by lia ].
Hint Extern 1 => lift_idx : lift_idx.
Ltac lift_idx_in h := first [ rewrite @lift_idx_recent in h by solve [ lia | eauto with lift_idx_hints ] | rewrite @lift_idx_old in h by lia ].
Ltac lift_idx_all := first [ rewrite @lift_idx_recent in * by solve [ lia | eauto with lift_idx_hints ] | rewrite @lift_idx_old in * by lia ].
Ltac destruct_lift_idx := match goal with |- context[@lift nat _ _ ?y ?x] => destruct (le_gt_dec y x); lift_idx end.
Instance LiftVar_idx: @LiftVar nat _ _.
Proof.
constructor.
just_do_it.
Instance LiftZero_idx: @LiftZero nat _.
Proof.
constructor.
just_do_it.
Instance LiftInjective_idx: @LiftInjective nat _.
Proof.
constructor.
just_do_it.
Instance LiftLift_idx: @LiftLift nat _.
Proof.
constructor.
just_do_it.
Instance LiftLiftFuse_idx: @LiftLiftFuse nat _.
Proof.
constructor.
just_do_it.
Ltac subst_idx := first [ rewrite @subst_idx_identity by lia | rewrite @subst_idx_miss_1 by lia | rewrite @subst_idx_miss_2 by lia ].
Ltac subst_idx_in h := first [ rewrite @subst_idx_identity in h by lia | rewrite @subst_idx_miss_1 in h by lia | rewrite @subst_idx_miss_2 in h by lia ].
Ltac subst_idx_all := first [ rewrite @subst_idx_identity in * by lia | rewrite @subst_idx_miss_1 in * by lia | rewrite @subst_idx_miss_2 in * by lia ].
Instance Lift_Traverse `{Var V, Traverse V T} : Lift T := { lift w k t := traverse (fun l x => var (lift w (l + k) x)) 0 t }.
Ltac plus_0_r := repeat match goal with |- context[?x + 0] => rewrite (plus_0_r x) end.
Ltac plus_0_r_in h := repeat match type of h with context[?x + 0] => rewrite (plus_0_r x) in h end.
Ltac recognize_lift := rewrite recognize_lift by eauto with typeclass_instances; repeat rewrite plus_0_l.
Ltac recognize_lift_in h := rewrite recognize_lift in h by eauto with typeclass_instances; repeat rewrite plus_0_l in h.
Ltac simpl_lift := match goal with (* Case: [_traverse] appears in the goal. *) (* this binds the meta-variable [_traverse] to the user's [traverse_term] *) |- context[?_traverse (fun l x : nat => var (lift ?w (l + ?k) x)) _ _] => (* this causes the reduction of the fixpoint: *) unfold _traverse; fold _traverse; (* we now have a term of the form [TApp (traverse_term ...) ...]. There remains to recognize the definition of [lift]. *) plus_0_r; (* useful when we have traversed a binder: 1 + 0 is 1 *) (* use [recognize_lift] at the specific type of the [_traverse] function that we have just simplified *) match type of _traverse with (nat -> nat -> ?V) -> nat -> ?T -> ?T => repeat rewrite (@recognize_lift V _ T _ _) by eauto with typeclass_instances end; repeat rewrite plus_0_l (* useful when [k1] is zero and we are at a leaf *) (* Case: [_traverse] appears in a hypothesis. *) (* this binds the meta-variable [_traverse] to the user's [traverse_term] *) | h: context[?_traverse (fun l x : nat => var (lift ?w (l + ?k) x)) _ _] |- _ => (* this causes the reduction of the fixpoint: *) unfold _traverse in h; fold _traverse in h; (* we now have a term of the form [TApp (traverse_term ...) ...]. There remains to recognize the definition of [lift]. *) plus_0_r_in h; (* useful when we have traversed a binder: 1 + 0 is 1 *) (* use [recognize_lift] at the specific type of the [_traverse] function that we have just simplified *) match type of _traverse with (nat -> nat -> ?V) -> nat -> ?T -> ?T => repeat rewrite (@recognize_lift V _ T _ _) in h by eauto with typeclass_instances end; repeat rewrite plus_0_l in h (* useful when [k1] is zero and we are at a leaf *) end.
Ltac simpl_lift_goal := (* this replaces [lift] with applications of [traverse] *) repeat rewrite @expand_lift; (* this replaces the generic [traverse] with the user's [_traverse] functions *) simpl (@traverse _ _ _); (* this simplifies applications of each [_traverse] function and folds them back *) repeat simpl_lift; (* if we have exposed applications of [lift_idx], try simplifying them away *) repeat lift_idx; (* if this exposes uses of [var], replace them with the user's [TVar] constructor *) simpl var.
Hint Extern 1 (lift _ _ _ = _) => simpl_lift_goal : simpl_lift_goal.
Hint Extern 1 (_ = lift _ _ _) => simpl_lift_goal : simpl_lift_goal.
Ltac simpl_lift_all := repeat rewrite @expand_lift in *; simpl (@traverse _ _ _) in *; repeat simpl_lift; repeat lift_idx_all; simpl var in *.
Ltac simpl_lift_in h := repeat rewrite @expand_lift in h; simpl (@traverse _ _ _) in h; repeat simpl_lift; repeat lift_idx_in h; simpl var in h.
Instance LiftVar_Traverse: forall `{Var V, Traverse V V}, TraverseIdentifiesVar -> @LiftVar V _ _.
Proof.
constructor.
unfold lift, Lift_Traverse.
intros.
rewrite traverse_identifies_var.
reflexivity.
Instance LiftZero_Traverse: forall `{Var V, Traverse V V}, TraverseVarIsIdentity -> @LiftZero V _.
Proof.
constructor.
intros.
unfold lift, Lift_Traverse.
rewrite traverse_var_is_identity.
reflexivity.
intros.
rewrite lift_zero.
reflexivity.
Instance LiftInjective_Traverse: forall `{Var V, Traverse V T}, TraverseVarInjective -> @LiftInjective T _.
Proof.
constructor.
unfold lift, Lift_Traverse.
intros w k.
intros.
eapply traverse_var_injective with (f := fun l x => lift w (l + k) x).
eauto using lift_injective.
eassumption.
Instance LiftLift_Traverse: forall `{Var V, Traverse V V, Traverse V T}, @TraverseFunctorial V _ T _ -> @TraverseRelative V T _ -> (* TraverseExtensional *) @TraverseIdentifiesVar V _ _ -> @LiftLift T _.
Proof.
constructor.
unfold lift, Lift_Traverse.
intros.
rewrite (traverse_traverse_var _ _ _).
rewrite (traverse_traverse_var _ _ _).
eapply (traverse_extensional _).
intros.
f_equal.
rewrite lift_lift by lia.
f_equal.
lia.
Instance LiftLiftFuse_Traverse: forall `{Var V, Traverse V V, Traverse V T}, @TraverseFunctorial V _ T _ -> @TraverseRelative V T _ -> (* TraverseExtensional *) @TraverseIdentifiesVar V _ _ -> @LiftLiftFuse T _.
Proof.
constructor.
unfold lift, Lift_Traverse.
intros.
rewrite (traverse_traverse_var _ _ _).
eapply (traverse_extensional _).
intros.
f_equal.
rewrite lift_lift_fuse by lia.
reflexivity.
Instance Subst_Traverse `{Var V, Traverse V V, Traverse V T} : Subst V T := { subst v k t := traverse (fun l x => subst_idx (lift l 0 v) (l + k) x) 0 t }.
Ltac recognize_subst := rewrite recognize_subst by eauto with typeclass_instances; try rewrite lift_zero; (* useful when [k1] is zero *) repeat rewrite plus_0_l.
Ltac recognize_subst_in h := rewrite recognize_subst in h by eauto with typeclass_instances; try rewrite lift_zero in h; (* useful when [k1] is zero *) repeat rewrite plus_0_l in h.
Ltac simpl_subst := match goal with (* Case: [_traverse] appears in the goal. *) (* this binds the meta-variable [_traverse] to the user's [traverse_term] *) |- context[?_traverse (fun l x : nat => subst_idx (lift l 0 ?v) (l + ?k) x) _ _] => (* this causes the reduction of the fixpoint: *) unfold _traverse; fold _traverse; (* we now have a term of the form [TApp (traverse_term ...) (traverse_term ...)]. There remains to recognize the definition of [subst]. *) plus_0_r; (* useful when we have traversed a binder: 1 + 0 is 1 *) (* use [recognize_subst] at the specific type of the [_traverse] function that we have just simplified *) match type of _traverse with (nat -> nat -> ?V) -> nat -> ?T -> ?T => repeat rewrite (@recognize_subst V _ _ T _ _ _ _ _) by eauto with typeclass_instances end; repeat rewrite plus_0_l; (* useful when [k1] is zero and we are at a leaf *) repeat rewrite lift_zero (* useful when [k1] is zero and we are at a leaf *) (* Case: [_traverse] appears in a hypothesis. *) (* this binds the meta-variable [_traverse] to the user's [traverse_term] *) | h: context[?_traverse (fun l x : nat => subst_idx (lift l 0 ?v) (l + ?k) x) _ _] |- _ => (* this causes the reduction of the fixpoint: *) unfold _traverse in h; fold _traverse in h; (* we now have a term of the form [TApp (traverse_term ...) (traverse_term ...)]. There remains to recognize the definition of [subst]. *) plus_0_r_in h; (* useful when we have traversed a binder: 1 + 0 is 1 *) (* use [recognize_subst] at the specific type of the [_traverse] function that we have just simplified *) match type of _traverse with (nat -> nat -> ?V) -> nat -> ?T -> ?T => repeat rewrite (@recognize_subst V _ _ T _ _ _ _ _) in h by eauto with typeclass_instances end; repeat rewrite plus_0_l in h; (* useful when [k1] is zero and we are at a leaf *) repeat rewrite lift_zero in h (* useful when [k1] is zero and we are at a leaf *) end.
Ltac simpl_subst_goal := (* this replaces [subst] with applications of [traverse] *) repeat rewrite @expand_subst; (* this replaces the generic [traverse] with the user's [_traverse] functions *) simpl (@traverse _ _ _); (* this simplifies applications of each [_traverse] function and folds them back *) repeat simpl_subst; (* if we have exposed applications of [subst_idx], try simplifying them away *) repeat subst_idx; (* if this exposes uses of [var], replace them with the user's [TVar] constructor *) simpl var.
Hint Extern 1 (subst _ _ _ = _) => simpl_subst_goal : simpl_subst_goal.
Hint Extern 1 (_ = subst _ _ _) => simpl_subst_goal : simpl_subst_goal.
Ltac simpl_subst_all := repeat rewrite @expand_subst in *; simpl (@traverse _ _ _) in *; repeat simpl_subst; repeat subst_idx_all; simpl var in *.
Ltac simpl_subst_in h := repeat rewrite @expand_subst in h; simpl (@traverse _ _ _) in h; repeat simpl_subst; repeat subst_idx_in h; simpl var in h.
Instance SubstVar_Traverse: forall `{Var V, Traverse V V}, TraverseIdentifiesVar -> TraverseVarIsIdentity -> SubstVar.
Proof.
constructor.
unfold subst, Subst_Traverse.
intros.
rewrite traverse_identifies_var.
rewrite lift_zero.
reflexivity.
Instance SubstLift_Traverse: forall `{Var V, Traverse V V, Traverse V T}, @TraverseFunctorial V _ T _ -> @TraverseIdentifiesVar V _ _ -> @TraverseVarIsIdentity V _ T _ -> @SubstLift T _ V _.
Proof.
constructor.
intros.
unfold lift, Lift_Traverse.
unfold subst, Subst_Traverse.
rewrite traverse_functorial.
eapply traverse_var_is_identity.
intros.
rewrite traverse_identifies_var.
just_do_it.
Instance LiftSubst1_Traverse: forall `{Var V, Traverse V V, Traverse V T}, @TraverseRelative V V _ -> @TraverseRelative V T _ -> (* TraverseExtensional *) @TraverseFunctorial V _ V _ -> @TraverseFunctorial V _ T _ -> @TraverseIdentifiesVar V _ _ -> @LiftSubst1 V _ T _ _.
Proof.
constructor.
intros.
unfold lift at 1 3.
unfold Lift_Traverse.
unfold subst, Subst_Traverse.
do 2 rewrite traverse_functorial.
eapply (traverse_extensional _).
intros.
rewrite traverse_identifies_var.
recognize_lift.
rewrite lift_lift by lia.
replace (l + (w + s)) with (w + (l + s)) by lia.
replace (lift w (l + k) x) with ((let (lift0) := Lift_idx in lift0) w (l + k) x) by (unfold lift; reflexivity).
unfold Lift_idx.
unfold subst_idx.
dblib_by_cases; try rewrite lift_var; just_do_it.
Instance LiftSubst2_Traverse: forall `{Var V, Traverse V V, Traverse V T}, @TraverseRelative V V _ -> @TraverseRelative V T _ -> (* TraverseExtensional *) @TraverseFunctorial V _ V _ -> @TraverseFunctorial V _ T _ -> @TraverseIdentifiesVar V _ _ -> @LiftSubst2 V _ T _ _.
Proof.
constructor.
intros.
unfold lift at 1 3.
unfold Lift_Traverse.
unfold subst, Subst_Traverse.
do 2 rewrite traverse_functorial.
eapply (traverse_extensional _).
intros.
rewrite traverse_identifies_var.
recognize_lift.
rewrite lift_lift by lia.
replace (l + (1 + k)) with (1 + (l + k)) by lia.
replace (lift w (1 + (l + k)) x) with ((let (lift0) := Lift_idx in lift0) w (1 + (l + k)) x) by (unfold lift; reflexivity).
unfold Lift_idx.
unfold subst_idx.
dblib_by_cases; try rewrite lift_var; just_do_it.
Instance LiftSubst_LiftSubst12 `{Lift V, Lift T, Subst V T} : LiftSubst1 -> LiftSubst2 -> LiftSubst.
Proof.
constructor.
intros.
destruct (le_gt_dec s k); do 2 lift_idx.
eapply lift_subst_2.
lia.
eapply lift_subst_1.
lia.
Instance SubstSubst_Traverse: forall `{Var V, Traverse V V, Traverse V T}, @TraverseRelative V V _ -> @TraverseRelative V T _ -> (* TraverseExtensional *) @TraverseIdentifiesVar V _ _ -> @TraverseVarIsIdentity V _ V _ -> @TraverseFunctorial V _ V _ -> @TraverseFunctorial V _ T _ -> @SubstSubst V _ _ T _.
Proof.
constructor.
intros.
unfold subst at 1 2 3 5.
unfold Subst_Traverse.
do 2 rewrite traverse_functorial.
eapply (traverse_extensional _).
intros.
do 2 recognize_subst.
rewrite lift_subst_1 by lia.
unfold subst_idx; dblib_by_cases; repeat rewrite subst_var; try solve [ just_do_it ].
subst_idx.
rewrite lift_lift by lia.
rewrite subst_lift.
reflexivity.
Instance Pun1_Traverse: forall `{Var V, Traverse V V, Traverse V T}, @TraverseFunctorial V _ T _ -> @TraverseVarIsIdentity V _ T _ -> @TraverseIdentifiesVar V _ _ -> @Pun1 V _ T _ _.
Proof.
constructor.
intros.
unfold lift, Lift_Traverse.
unfold subst, Subst_Traverse.
rewrite traverse_functorial.
rewrite traverse_var_is_identity.
reflexivity.
intros.
rewrite traverse_identifies_var.
rewrite lift_var.
just_do_it.
Instance Pun2_Traverse: forall `{Var V, Traverse V V, Traverse V T}, @TraverseFunctorial V _ T _ -> @TraverseVarIsIdentity V _ T _ -> @TraverseIdentifiesVar V _ _ -> @Pun2 V _ T _ _.
Proof.
constructor.
intros.
unfold lift, Lift_Traverse.
unfold subst, Subst_Traverse.
rewrite traverse_functorial.
rewrite traverse_var_is_identity.
reflexivity.
intros.
rewrite traverse_identifies_var.
rewrite lift_var.
just_do_it.
Instance PunPun_Traverse: forall `{Var V, Traverse V V, Traverse V T}, @TraverseRelative V T _ -> (* TraverseExtensional *) @TraverseFunctorial V _ T _ -> @TraverseIdentifiesVar V _ _ -> @PunPun V _ T _ _.
Proof.
constructor.
intros.
unfold lift, Lift_Traverse.
unfold subst, Subst_Traverse.
do 2 rewrite traverse_functorial.
eapply (traverse_extensional _).
intros.
do 2 rewrite traverse_identifies_var.
just_do_it.
Ltac fold_closed_hyps := repeat match goal with h: shift _ ?t = ?t |- _ => generalize (fold_closed _ h); clear h; intro h end.
Ltac inversion_closed_in_internal h := (* Unfold the definition of [closed]. This exposes [lift]. *) unfold closed in h; (* If [lift] is applied to a constructor, simplify it. *) rewrite expand_lift in h; simpl (@traverse _ _ _) in h; simpl_lift; (* This may result in an equality that involves two constructors. Decompose it. *) try (injection h; clear h; intros).
Ltac inversion_closed_in h := inversion_closed_in_internal h; fold_closed_hyps.
Ltac inversion_closed := repeat match goal with h: closed _ _ |- _ => inversion_closed_in_internal h end; fold_closed_hyps.
Hint Extern 1 => f_equal : construction_closed.
Ltac construction_closed := solve [ (* Expose the definition of [closed] in terms of [lift]. *) unfold closed in *; (* Presumably [lift] is applied to a constructor in the goal. Simplify it. *) simpl_lift_goal; (* If we are looking at a variable, the equation should look like this: [var (shift k x) = var x]. Simplify [var] away, and apply the tactic [lift_idx] to simplify [shift] away. *) try (simpl; lift_idx); (* Conclude. *) eauto with lia construction_closed ].
Hint Extern 1 (shift ?x ?v = ?v) => solve [ eapply closed_monotonic; [ eauto with typeclass_instances (* LiftLift *) | construction_closed (* [v] is [k]-closed *) | lia (* [k <= x] *) ] ] : shift_closed.
Ltac shift_closed := match goal with h: closed ?x ?v |- context[shift ?x ?v] => replace (shift x v) with v (* no subgoals are generated; apparently the hypothesis [h] allows Coq to recognize that these terms are equal *) end.
Hint Extern 1 (subst ?w ?x ?v = ?v) => solve [ eapply closed_subst_invariant; [ eauto with typeclass_instances | eauto with typeclass_instances | construction_closed | lia ] ] : subst_closed.
Instance Rotate1SelfInverse_Algebraic: forall `{Var V, Lift V, Lift T, Subst V V, Subst V T}, @LiftVar V _ _ -> @SubstVar V _ _ -> @LiftLift T _ -> @LiftSubst2 V _ T _ _ -> @SubstSubst V _ _ T _ -> @Pun2 V _ T _ _ -> @Rotate1SelfInverse V _ T _ _.
Proof.
constructor.
intro.
unfold rotate.
rewrite lift_subst_2 by lia.
rewrite <- lift_lift by lia.
rewrite lift_var.
simpl.
rewrite subst_subst by lia.
rewrite subst_var.
rewrite lift_var.
subst_idx.
simpl.
replace (@var V _ 2) with (shift 1 (@var V _ 1)) by (rewrite lift_var; auto).
rewrite <- lift_subst_2 by lia.
rewrite pun_2.
rewrite pun_2.
reflexivity.
Instance Rotate1SelfInverse_Traverse: forall `{Var V, Traverse V V, Traverse V T}, @TraverseVarIsIdentity V _ T _ -> @TraverseIdentifiesVar V _ _ -> @TraverseFunctorial V _ T _ -> @Rotate1SelfInverse V _ T _ _.
Proof.
constructor.
intros.
unfold rotate, subst, lift, Subst_Traverse, Lift_Traverse.
do 3 rewrite traverse_functorial.
apply traverse_var_is_identity.
intros l x.
rewrite traverse_identifies_var.
rewrite lift_var.
rewrite subst_idx_var.
do 2 rewrite traverse_identifies_var.
rewrite lift_var.
rewrite subst_idx_var.
f_equal.
just_do_it.
Ltac prove_traverse_identifies_var := reflexivity.
Ltac prove_traverse_var_injective := let t1 := fresh "t1" in intros ? ? t1; induction t1; let t2 := fresh "t2" in intro t2; destruct t2; simpl; let h := fresh "h" in intros ? h; inversion h; f_equal; eauto using @traverse_var_injective with typeclass_instances.
Ltac prove_traverse_functorial := let t := fresh "t" in intros ? ? t; induction t; intros; simpl; f_equal; eauto using @traverse_functorial with typeclass_instances.
Ltac prove_traverse_relative := let t := fresh "t" in intros ? ? ? t; induction t; intros; subst; simpl; eauto using @traverse_relative with f_equal lia typeclass_instances.
Ltac prove_traverse_var_is_identity := intros ? ? t; induction t; intros; simpl; f_equal; eauto using @traverse_var_is_identity with typeclass_instances.
Ltac lift_lift_hint := first [ rewrite lift_lift by lia; reflexivity | rewrite <- lift_lift by lia; reflexivity | rewrite lift_lift by lia | rewrite <- lift_lift by lia ].
Hint Extern 1 (_ = lift _ _ (lift _ _ _)) => lift_lift_hint : lift_lift.
Hint Extern 1 (lift _ _ (lift _ _ _) = _) => lift_lift_hint : lift_lift.
Ltac subst_lift_hint := first [ rewrite subst_lift; reflexivity | rewrite subst_lift ].
Hint Extern 1 (subst _ _ (lift _ _ _) = _) => subst_lift_hint : subst_lift.
Hint Extern 1 (_ = subst _ _ (lift _ _ _)) => subst_lift_hint : subst_lift.
Hint Extern 1 (subst _ _ _ = _) => subst_lift_hint : subst_lift.
Hint Extern 1 (_ = subst _ _ _) => subst_lift_hint : subst_lift.
Ltac lift_subst_hint := first [ rewrite lift_subst_1 by lia; reflexivity | rewrite lift_subst_2 by lia; reflexivity | rewrite <- lift_subst_1 by lia; reflexivity | rewrite <- lift_subst_2 by lia; reflexivity | rewrite lift_subst_1 by lia | rewrite lift_subst_2 by lia | rewrite <- lift_subst_1 by lia | rewrite <- lift_subst_2 by lia ].
Hint Extern 1 (_ = lift _ _ (subst _ _ _)) => lift_subst_hint : lift_subst.
Hint Extern 1 (lift _ _ (subst _ _ _) = _) => lift_subst_hint : lift_subst.
Hint Extern 1 (_ = lift _ _ (lift _ _ (subst _ _ _))) => do 2 lift_subst_hint : lift_subst.
Hint Extern 1 (lift _ _ (lift _ _ (subst _ _ _)) = _) => do 2 lift_subst_hint : lift_subst.
Hint Extern 1 (lift _ _ _ = subst (lift _ _ _) _ (lift _ _ _)) => lift_subst_hint : lift_subst.
Ltac subst_subst_hint := first [ rewrite subst_subst by lia; reflexivity | rewrite <- subst_subst by lia; reflexivity | rewrite subst_subst by lia | rewrite <- subst_subst by lia ].
Hint Extern 1 (_ = subst _ _ (subst _ _ _)) => subst_subst_hint : subst_subst.
Hint Extern 1 (subst _ _ (subst _ _ _) = _) => subst_subst_hint : subst_subst.
Ltac lift_lift_fuse_hint := rewrite lift_lift_fuse by lia.
Hint Extern 1 (lift _ _ (lift _ _ _) = _) => lift_lift_fuse_hint : lift_lift_fuse.
Hint Extern 1 (_ = lift _ _ (lift _ _ _)) => lift_lift_fuse_hint : lift_lift_fuse.
Hint Extern 1 (lift ?wk _ _ = lift (S ?wk) _ _) => eapply lift_lift_fuse_successor : lift_lift_fuse_successor.
Ltac iterated_lift := first [ rewrite lift_zero | rewrite <- lift_lift_fuse_successor ].
Global Opaque lift.
Global Opaque subst.

Lemma lift_lift_reversed: forall `{Lift T}, LiftLift -> forall wk k ws s t, k >= s + ws -> lift wk k (lift ws s t) = lift ws s (lift wk (k - ws) t).
Proof.
intros.
replace k with (ws + (k - ws)) by lia.
erewrite <- lift_lift by lia.
replace (ws + (k - ws) - ws) with (k - ws) by lia.
Admitted.

Lemma traverse_extensional: forall `{Traverse V T}, TraverseRelative -> forall f g, (forall l x, f l x = g l x) -> forall t l, traverse f l t = traverse g l t.
Proof.
intros.
eapply traverse_relative with (p := 0).
intros m ?.
replace (m + 0) with m by lia.
eauto.
Admitted.

Lemma traverse_traverse_var: forall `{Var V, Traverse V V, Traverse V T}, @TraverseFunctorial V _ T _ -> @TraverseRelative V T _ -> (* TraverseExtensional *) @TraverseIdentifiesVar V _ _ -> forall f g t l, traverse g l (traverse_var f l t) = traverse (fun l x => g l (f l x)) l t.
Proof.
intros.
rewrite traverse_functorial.
eapply (traverse_extensional _).
Admitted.

Lemma lift_idx_recent: forall w k x, k > x -> lift w k x = x.
Proof.
Admitted.

Lemma lift_idx_old: forall w k x, k <= x -> lift w k x = w + x.
Proof.
Admitted.

Instance LiftVar_idx: @LiftVar nat _ _.
Proof.
constructor.
Admitted.

Instance LiftZero_idx: @LiftZero nat _.
Proof.
constructor.
Admitted.

Instance LiftInjective_idx: @LiftInjective nat _.
Proof.
constructor.
Admitted.

Instance LiftLift_idx: @LiftLift nat _.
Proof.
constructor.
Admitted.

Instance LiftLiftFuse_idx: @LiftLiftFuse nat _.
Proof.
constructor.
Admitted.

Lemma subst_idx_miss_1: forall `{Var V} v k x, k > x -> subst_idx v k x = var x.
Proof.
Admitted.

Lemma subst_idx_identity: forall `{Var V} v k x, k = x -> subst_idx v k x = v.
Proof.
Admitted.

Lemma subst_idx_miss_2: forall `{Var V} v k x, k < x -> subst_idx v k x = var (x - 1).
Proof.
Admitted.

Lemma subst_idx_var: forall `{Var V}, forall v k x, subst_idx (var v) k x = var (subst_idx v k x).
Proof.
Admitted.

Lemma expand_lift: forall `{Var V, Traverse V T}, forall w k t, lift w k t = traverse (fun l x => var (lift w (l + k) x)) 0 t.
Proof.
Admitted.

Lemma recognize_lift: forall `{Var V, Traverse V T}, TraverseRelative -> forall w k1 k2 t, forall traverse_, traverse_ = traverse -> (* helps rewrite *) traverse_ (fun l x => var (lift w (l + k2) x)) k1 t = lift w (k1 + k2) t.
Proof.
intros.
subst.
simpl.
eapply traverse_relative; [ | instantiate (1 := k1); lia ].
Admitted.

Instance LiftVar_Traverse: forall `{Var V, Traverse V V}, TraverseIdentifiesVar -> @LiftVar V _ _.
Proof.
constructor.
unfold lift, Lift_Traverse.
intros.
rewrite traverse_identifies_var.
Admitted.

Instance LiftZero_Traverse: forall `{Var V, Traverse V V}, TraverseVarIsIdentity -> @LiftZero V _.
Proof.
constructor.
intros.
unfold lift, Lift_Traverse.
rewrite traverse_var_is_identity.
reflexivity.
intros.
rewrite lift_zero.
Admitted.

Instance LiftInjective_Traverse: forall `{Var V, Traverse V T}, TraverseVarInjective -> @LiftInjective T _.
Proof.
constructor.
unfold lift, Lift_Traverse.
intros w k.
intros.
eapply traverse_var_injective with (f := fun l x => lift w (l + k) x).
eauto using lift_injective.
Admitted.

Instance LiftLift_Traverse: forall `{Var V, Traverse V V, Traverse V T}, @TraverseFunctorial V _ T _ -> @TraverseRelative V T _ -> (* TraverseExtensional *) @TraverseIdentifiesVar V _ _ -> @LiftLift T _.
Proof.
constructor.
unfold lift, Lift_Traverse.
intros.
rewrite (traverse_traverse_var _ _ _).
rewrite (traverse_traverse_var _ _ _).
eapply (traverse_extensional _).
intros.
f_equal.
rewrite lift_lift by lia.
f_equal.
Admitted.

Lemma expand_subst: forall `{Var V, Traverse V V, Traverse V T}, forall v k t, subst v k t = traverse (fun l x => subst_idx (lift l 0 v) (l + k) x) 0 t.
Proof.
Admitted.

Lemma recognize_subst: forall `{Var V, Traverse V V, Traverse V T}, @TraverseFunctorial V _ V _ -> @TraverseIdentifiesVar V _ _ -> @TraverseRelative V V _ -> @TraverseRelative V T _ -> forall traverse_, traverse_ = traverse -> (* helps rewrite *) forall v k2 k1 t, traverse_ (fun l x => subst_idx (lift l 0 v) (l + k2) x) k1 t = subst (lift k1 0 v) (k1 + k2) t.
Proof.
intros.
subst.
unfold subst, Subst_Traverse.
eapply traverse_relative; [ | instantiate (1 := k1); lia ].
intros.
f_equal.
rewrite lift_lift_fuse by lia.
reflexivity.
Admitted.

Instance SubstVar_Traverse: forall `{Var V, Traverse V V}, TraverseIdentifiesVar -> TraverseVarIsIdentity -> SubstVar.
Proof.
constructor.
unfold subst, Subst_Traverse.
intros.
rewrite traverse_identifies_var.
rewrite lift_zero.
Admitted.

Instance SubstLift_Traverse: forall `{Var V, Traverse V V, Traverse V T}, @TraverseFunctorial V _ T _ -> @TraverseIdentifiesVar V _ _ -> @TraverseVarIsIdentity V _ T _ -> @SubstLift T _ V _.
Proof.
constructor.
intros.
unfold lift, Lift_Traverse.
unfold subst, Subst_Traverse.
rewrite traverse_functorial.
eapply traverse_var_is_identity.
intros.
rewrite traverse_identifies_var.
Admitted.

Instance LiftSubst1_Traverse: forall `{Var V, Traverse V V, Traverse V T}, @TraverseRelative V V _ -> @TraverseRelative V T _ -> (* TraverseExtensional *) @TraverseFunctorial V _ V _ -> @TraverseFunctorial V _ T _ -> @TraverseIdentifiesVar V _ _ -> @LiftSubst1 V _ T _ _.
Proof.
constructor.
intros.
unfold lift at 1 3.
unfold Lift_Traverse.
unfold subst, Subst_Traverse.
do 2 rewrite traverse_functorial.
eapply (traverse_extensional _).
intros.
rewrite traverse_identifies_var.
recognize_lift.
rewrite lift_lift by lia.
replace (l + (w + s)) with (w + (l + s)) by lia.
replace (lift w (l + k) x) with ((let (lift0) := Lift_idx in lift0) w (l + k) x) by (unfold lift; reflexivity).
unfold Lift_idx.
unfold subst_idx.
Admitted.

Instance LiftSubst2_Traverse: forall `{Var V, Traverse V V, Traverse V T}, @TraverseRelative V V _ -> @TraverseRelative V T _ -> (* TraverseExtensional *) @TraverseFunctorial V _ V _ -> @TraverseFunctorial V _ T _ -> @TraverseIdentifiesVar V _ _ -> @LiftSubst2 V _ T _ _.
Proof.
constructor.
intros.
unfold lift at 1 3.
unfold Lift_Traverse.
unfold subst, Subst_Traverse.
do 2 rewrite traverse_functorial.
eapply (traverse_extensional _).
intros.
rewrite traverse_identifies_var.
recognize_lift.
rewrite lift_lift by lia.
replace (l + (1 + k)) with (1 + (l + k)) by lia.
replace (lift w (1 + (l + k)) x) with ((let (lift0) := Lift_idx in lift0) w (1 + (l + k)) x) by (unfold lift; reflexivity).
unfold Lift_idx.
unfold subst_idx.
Admitted.

Instance LiftSubst_LiftSubst12 `{Lift V, Lift T, Subst V T} : LiftSubst1 -> LiftSubst2 -> LiftSubst.
Proof.
constructor.
intros.
destruct (le_gt_dec s k); do 2 lift_idx.
eapply lift_subst_2.
lia.
eapply lift_subst_1.
Admitted.

Instance SubstSubst_Traverse: forall `{Var V, Traverse V V, Traverse V T}, @TraverseRelative V V _ -> @TraverseRelative V T _ -> (* TraverseExtensional *) @TraverseIdentifiesVar V _ _ -> @TraverseVarIsIdentity V _ V _ -> @TraverseFunctorial V _ V _ -> @TraverseFunctorial V _ T _ -> @SubstSubst V _ _ T _.
Proof.
constructor.
intros.
unfold subst at 1 2 3 5.
unfold Subst_Traverse.
do 2 rewrite traverse_functorial.
eapply (traverse_extensional _).
intros.
do 2 recognize_subst.
rewrite lift_subst_1 by lia.
unfold subst_idx; dblib_by_cases; repeat rewrite subst_var; try solve [ just_do_it ].
subst_idx.
rewrite lift_lift by lia.
rewrite subst_lift.
Admitted.

Instance Pun1_Traverse: forall `{Var V, Traverse V V, Traverse V T}, @TraverseFunctorial V _ T _ -> @TraverseVarIsIdentity V _ T _ -> @TraverseIdentifiesVar V _ _ -> @Pun1 V _ T _ _.
Proof.
constructor.
intros.
unfold lift, Lift_Traverse.
unfold subst, Subst_Traverse.
rewrite traverse_functorial.
rewrite traverse_var_is_identity.
reflexivity.
intros.
rewrite traverse_identifies_var.
rewrite lift_var.
Admitted.

Instance Pun2_Traverse: forall `{Var V, Traverse V V, Traverse V T}, @TraverseFunctorial V _ T _ -> @TraverseVarIsIdentity V _ T _ -> @TraverseIdentifiesVar V _ _ -> @Pun2 V _ T _ _.
Proof.
constructor.
intros.
unfold lift, Lift_Traverse.
unfold subst, Subst_Traverse.
rewrite traverse_functorial.
rewrite traverse_var_is_identity.
reflexivity.
intros.
rewrite traverse_identifies_var.
rewrite lift_var.
Admitted.

Instance PunPun_Traverse: forall `{Var V, Traverse V V, Traverse V T}, @TraverseRelative V T _ -> (* TraverseExtensional *) @TraverseFunctorial V _ T _ -> @TraverseIdentifiesVar V _ _ -> @PunPun V _ T _ _.
Proof.
constructor.
intros.
unfold lift, Lift_Traverse.
unfold subst, Subst_Traverse.
do 2 rewrite traverse_functorial.
eapply (traverse_extensional _).
intros.
do 2 rewrite traverse_identifies_var.
Admitted.

Lemma closed_increment: forall `{Lift T}, LiftLift -> forall k t, closed k t -> closed (1 + k) t.
Proof.
unfold closed.
intros.
match goal with h: shift _ _ = _ |- _ => rewrite <- h at 1 end.
rewrite <- lift_lift by lia.
Admitted.

Lemma closed_monotonic: forall `{Lift T}, LiftLift -> forall k t, closed k t -> forall j, j >= k -> closed j t.
Proof.
do 6 intro.
assert (forall i, closed (i + k) t).
induction i.
assumption.
replace (S i + k) with (1 + (i + k)) by lia.
eauto using closed_increment with typeclass_instances.
intros j ?.
replace j with ((j - k) + k) by lia.
Admitted.

Lemma closed_lift_invariant: forall `{Lift T}, forall { _ : LiftZero }, forall { _ : LiftLift }, forall { _ : LiftLiftFuse }, forall k t, closed k t -> forall j, j >= k -> forall w, lift w j t = t.
Proof.
induction w.
eauto using lift_zero.
change (S w) with (1 + w).
erewrite <- lift_lift_fuse by (instantiate (1 := j); lia).
rewrite IHw.
Admitted.

Lemma closed_subst_invariant: forall `{Lift T, Subst V T}, forall { _ : LiftLift}, forall { _ : SubstLift}, forall k t, closed k t -> forall j, j >= k -> forall v, subst v j t = t.
Proof.
intros.
assert (h: shift j t = t).
eapply closed_monotonic; eauto.
rewrite <- h at 1.
Admitted.

Lemma closed_var: forall k x : nat, x >= k -> closed k x -> False.
Proof.
unfold closed.
Admitted.

Lemma lift_preserves_closed: forall `{Lift T}, @LiftLift T _ -> forall k (t : T), closed k t -> closed (S k) (shift 0 t).
Proof.
unfold closed.
intros.
change (S k) with (1 + k).
rewrite <- lift_lift by lia.
Admitted.

Lemma subst_preserves_closed: forall `{Lift V, Lift T, Subst V T}, @LiftSubst2 V _ T _ _ -> forall k (v : V) (t : T), closed k v -> closed (S k) t -> closed k (subst v 0 t).
Proof.
unfold closed.
intros.
rewrite lift_subst_2 by lia.
simpl.
change (1 + k) with (S k).
Admitted.

Lemma fold_closed: forall `{Lift T}, forall k t, shift k t = t -> closed k t.
Proof.
Admitted.

Lemma rotate_characterization: forall n k, (k = 0 -> rotate n k = n) /\ (k > 0 -> k <= n -> rotate n k = k - 1) /\ (k > n -> rotate n k = k).
Proof.
Admitted.

Instance LiftLiftFuse_Traverse: forall `{Var V, Traverse V V, Traverse V T}, @TraverseFunctorial V _ T _ -> @TraverseRelative V T _ -> (* TraverseExtensional *) @TraverseIdentifiesVar V _ _ -> @LiftLiftFuse T _.
Proof.
constructor.
unfold lift, Lift_Traverse.
intros.
rewrite (traverse_traverse_var _ _ _).
eapply (traverse_extensional _).
intros.
f_equal.
rewrite lift_lift_fuse by lia.
reflexivity.
