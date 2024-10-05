Require Import Relation_Operators Operators_Properties Lia PeanoNat List.
Import ListNotations.
Require Undecidability.CounterMachines.CM1.
Module CM := CM1.
Require Undecidability.CounterMachines.Util.CM1_facts.
Module CM_facts := CM1_facts.
Require Undecidability.StackMachines.Reductions.CM1_HALT_to_SMNdl_UB.SMX.
Require Import Undecidability.StackMachines.Reductions.CM1_HALT_to_SMNdl_UB.SMX_facts.
Module SM := SMX.
From Undecidability.StackMachines.Util Require Import Facts Nat_facts List_facts.
Require Import ssreflect ssrbool ssrfun.
Set Default Proof Using "Type".
Set Default Goal Selector "!".
Local Arguments in_combine_l {A B l l' x y}.
Local Arguments in_combine_r {A B l l' x y}.
Inductive Prefix : Set := Try | Yes | No.
Inductive BasicState : Set := (* is_bounded false ask boundedness, is_bounded true is positive answer *) | is_bounded : bool -> BasicState (* #?i tries operation at index i; #+i performs operation at index i; #-i continues with next operation *) | index : Prefix -> CM.State -> BasicState (* $?i to increase counter for current operation index i; $+i has successfully increased counter for current operation index i; $-i failed to increase counter for current operation index i *) | increase : Prefix -> CM.State -> BasicState.
Inductive State : Set := | basic_state : BasicState -> State (* goto n X Y travels in steps of size (n+1) over 0s if successful goes to X, on failure goes to Y *) | goto : nat -> BasicState -> BasicState -> State.
Inductive Symbol : Set := zero : Symbol | one : Symbol.
Local Notation "'#? i" := (basic_state (index Try i)) (at level 50).
Local Notation "'#+ i" := (basic_state (index Yes i)) (at level 50).
Local Notation "'#- i" := (basic_state (index No i)) (at level 50).
Local Notation "#? i" := (index Try i) (at level 50).
Local Notation "#+ i" := (index Yes i) (at level 50).
Local Notation "#- i" := (index No i) (at level 50).
Local Notation "'$? i" := (basic_state (increase Try i)) (at level 50).
Local Notation "'$+ i" := (basic_state (increase Yes i)) (at level 50).
Local Notation "'$- i" := (basic_state (increase No i)) (at level 50).
Local Notation "$? i" := (increase Try i) (at level 50).
Local Notation "$+ i" := (increase Yes i) (at level 50).
Local Notation "$- i" := (increase No i) (at level 50).
Local Notation "'?|" := (basic_state (is_bounded false)).
Local Notation "'+|" := (basic_state (is_bounded true)).
Local Notation "?|" := (is_bounded false).
Local Notation "+|" := (is_bounded true).
Local Notation "§0" := (zero).
Local Notation "§1" := (one).
Local Notation "§0^ n" := (repeat §0 n) (at level 10, format "§0^ n").
Opaque Nat.add Nat.mul List.app List.repeat.
Definition nat_norm := (Nat.add_0_r, Nat.add_0_l, Nat.sub_0_r, Nat.sub_diag, Nat.mul_1_r, Nat.mul_1_l, Nat.mod_1_r).
Definition app_norm := (app_nil_l, app_nil_r, @app_assoc', @repeat_appP, @repeat_app_appP, @repeat_singP _ §0, @cons_repeat_app _ §0).
Section Reduction.
Variable P : CM.Cm1.
Variable capped_P : Forall (fun '(_, n) => n < 4) P.
Definition iP : list (CM.State * (CM.State * nat)) := combine (seq 0 (length P)) P.
Definition gotos : list (nat * BasicState * BasicState) := (* goto n #+i #-i *) map (fun '(i, (j, n)) => (n, #+i, #-i)) iP ++ (* goto #?(i+1)*) map (fun '(i, (j, n)) => (0, #?(1+(i:CM.State)), #?(1+(i:CM.State)))) iP ++ (* goto $?i*) map (fun '(i, (j, n)) => (0, $?i, $?i)) iP ++ (* goto $+i*) map (fun '(i, (j, n)) => (0, $+i, $+i)) iP ++ (* goto $-i*) map (fun '(i, (j, n)) => (0, $-i, $-i)) iP ++ (* goto +| *) [(0, +|, +|)].
Definition igotos : list (nat * (CM.State * BasicState * BasicState)) := combine (seq 0 (length gotos)) gotos.
Definition G := length gotos + 4.
Local Definition SMX := SM.SMX (State := State) (Symbol := Symbol).
Local Definition Instruction := SM.Instruction (State := State) (Symbol := Symbol).
Local Definition Config := SM.Config (State := State) (Symbol := Symbol).
Definition index_try_spec : nat * (CM.State * nat) -> Instruction := (fun '(i, (j, n)) => (([§1], [§0], '#?i), ([§1], [§0], goto n (#+i) (#-i)), false)).
Definition index_no_spec : nat * (CM.State * nat) -> Instruction := (fun '(i, (j, n)) => (([], [§0], '#-i), ([], [§0], goto 0 (#? (1+i)) (#? (1+i))), false)).
Definition index_yes_spec_1 : nat * (CM.State * nat) -> Instruction := (fun '(i, (j, n)) => (([], [§1], '#+i), ([], [§1], ('#? j)), true)).
Definition index_yes_spec_n1 : nat * (CM.State * nat) -> Instruction := (fun '(i, (j, n)) => (([], repeat §0 (1+n), '#+i), (repeat §0 n, [§1], goto 0 ($?i) ($?i)), true)).
Definition increase_try_spec_0 : nat * (CM.State * nat) -> Instruction := (fun '(i, (j, n)) => (([§1] ++ [§0], [], '$?i), ([§1], [§0], goto 0 ($+i) ($+i)), false)).
Definition increase_try_spec_1 : nat * (CM.State * nat) -> Instruction := (fun '(i, (j, n)) => (([§1] ++ [§1], [], '$?i), ([§1], [§0], goto 0 ($-i) ($-i)), false)).
Definition increase_yes_spec : nat * (CM.State * nat) -> Instruction := (fun '(i, (j, n)) => (([§1], [], '$+i), ([], [§0], '#+i), true)).
Definition increase_no_spec : nat * (CM.State * nat) -> Instruction := (fun '(i, (j, n)) => (([§1], [], '$-i), ([], [§0], goto 0 +| +|), true)).
Definition goto_spec_G : _ -> Instruction := (fun '(i, (n, X, Y)) => (([], §0^G, goto n X Y), ([§1] ++ §0^i ++ [§1] ++ §0^(G-2-i), [], '?|), true)).
Definition goto_spec_1 : nat -> (nat * (nat * BasicState * BasicState)) -> Instruction := (fun m '(i, (n, X, Y)) => (([], §0^m ++ [§1], goto n X Y), (§0^m, [§1], basic_state (if m mod (n+1) is 0 then X else Y)), true)).
Definition bound_yes_spec : _ -> Instruction := (fun '(i, (n, X, Y)) => (([§1] ++ §0^i ++ [§1] ++ §0^(G-2-i), [], '+|), (§0^(n+1), §0^(G-(n+1)), goto n X Y), false)).
Definition bound_try_spec_1 : Instruction := (([§1], [§1], '?|), ([§1], [§1], '+|), true).
Definition bound_try_spec_01 : Instruction := (([§0] ++ [§1], [§1], '?|), ([§0] ++ [§1], [§1], '+|), true).
Definition bound_try_spec_00 : Instruction := (([§0] ++ [§0], [§1], '?|), ([§0] ++ [§1], [§1], '#?0), true).
Definition bound_try_spec : list Instruction := [bound_try_spec_1] ++ [bound_try_spec_01] ++ [bound_try_spec_00].
Definition index_ops : list Instruction := map index_try_spec iP ++ map index_no_spec iP ++ map index_yes_spec_1 iP ++ map index_yes_spec_n1 iP.
Definition increase_ops : list Instruction := map increase_try_spec_0 iP ++ map increase_try_spec_1 iP ++ map increase_yes_spec iP ++ map increase_no_spec iP.
Definition goto_ops : list Instruction := map goto_spec_G igotos ++ flat_map (fun m => map (goto_spec_1 m) igotos) (seq 0 G).
Definition bound_ops : list Instruction := map bound_yes_spec igotos ++ bound_try_spec.
Definition M : SMX := locked index_ops ++ locked increase_ops ++ locked goto_ops ++ locked bound_ops.
Local Hint Immediate in_goto_spec_1_M in_goto_spec_G_M in_index_try_spec_M in_index_no_spec_M in_index_yes_spec_1_M in_index_yes_spec_n1_M in_increase_try_spec_0_M in_increase_try_spec_1_M in_increase_yes_spec_M in_increase_no_spec_M in_bound_try_spec_1_M in_bound_try_spec_01_M in_bound_try_spec_00_M in_bound_yes_spec_M in_scan_gotos in_next_gotos in_try_gotos in_yes_gotos in_no_gotos in_bound_gotos : M.
Inductive step_spec (X Y: Config) : Prop := | index_try_step_spec v w i j n : X = ([§1] ++ v, [§0] ++ w, '#?i) -> Y = ([§1] ++ v, [§0] ++ w, goto n (#+i) (#-i)) -> In (i, (j, n)) iP -> step_spec X Y | index_no_step_spec v w i j n : X = (v, [§0] ++ w, '#-i) -> Y = (v, [§0] ++ w, goto 0 (#? (1+i)) (#? (1+i))) -> In (i, (j, n)) iP -> step_spec X Y | index_yes_step_spec_1 v w i j n : X = (v, [§1] ++ w, '#+i) -> Y = ([§1] ++ w, v, '#?j) -> In (i, (j, n)) iP -> step_spec X Y | index_yes_step_spec_n1 v w i j n : X = (v, repeat §0 (1+n) ++ w, '#+i) -> Y = ([§1] ++ w, repeat §0 n ++ v, goto 0 ($?i) ($?i)) -> In (i, (j, n)) iP -> step_spec X Y | increase_try_step_spec_0 v w i j n : X = ([§1] ++ [§0] ++ v, w, '$?i) -> Y = ([§1] ++ v, [§0] ++ w, goto 0 ($+i) ($+i)) -> In (i, (j, n)) iP -> step_spec X Y | increase_try_step_spec_1 v w i j n : X = ([§1] ++ [§1] ++ v, w, '$?i) -> Y = ([§1] ++ v, [§0] ++ w, goto 0 ($-i) ($-i)) -> In (i, (j, n)) iP -> step_spec X Y | increase_yes_step_spec v w i j n : X = ([§1] ++ v, w, '$+i) -> Y = ([§0] ++ w, v, '#+i) -> In (i, (j, n)) iP -> step_spec X Y | increase_no_step_spec v w i j n : X = ([§1] ++ v, w, '$-i) -> Y = ([§0] ++ w, v, goto 0 +| +|) -> In (i, (j, n)) iP -> step_spec X Y | goto_step_spec_G v w i n' X' Y' : X = (v, §0^G ++ w, goto n' X' Y') -> Y = (w, [§1] ++ §0^i ++ [§1] ++ §0^(G-2-i) ++ v, '?|) -> In (i, (n', X', Y')) igotos -> step_spec X Y | goto_step_spec_1 v w m i n' X' Y' : X = (v, §0^m ++ [§1] ++ w, goto n' X' Y') -> Y = ([§1] ++ w, §0^m ++ v, basic_state (if m mod (n'+1) is 0 then X' else Y')) -> In (i, (n', X', Y')) igotos -> m < G -> step_spec X Y | bound_yes_step_spec v w i n' X' Y' : X = ([§1] ++ §0^i ++ [§1] ++ §0^(G-2-i) ++ v, w, '+|) -> Y = (§0^(n'+1) ++ v, §0^(G-(n'+1)) ++ w, goto n' X' Y') -> In (i, (n', X', Y')) igotos -> step_spec X Y | bound_try_step_spec_1 v w : X = ([§1] ++ v, [§1] ++ w, '?|) -> Y = ([§1] ++ w, [§1] ++ v, '+|) -> step_spec X Y | bound_try_step_spec_01 v w : X = ([§0] ++ [§1] ++ v, [§1] ++ w, '?|) -> Y = ([§1] ++ w, [§0] ++ [§1] ++ v, '+|) -> step_spec X Y | bound_try_step_spec_00 v w : X = ([§0] ++ [§0] ++ v, [§1] ++ w, '?|) -> Y = ([§1] ++ w, [§0] ++ [§1] ++ v, '#?0) -> step_spec X Y.
Local Definition reachable_n := reachable_n M.
Definition gotos_index (X Y: BasicState ) : nat := match X, Y with | #+ i, #- j => i | #? i, #? j => length P + (i-1) | $? i, $? j => length P * 2 + i | $+ i, $+ j => length P * 3 + i | $- i, $- j => length P * 4 + i | _, _ => length P * 5 end.
Local Definition transition := SM.transition (State := State) (Symbol := Symbol).
Ltac unify_iP := match goal with H1 : In (?i, (?j1, ?n1)) iP, H2 : In (?i, (?j2, ?n2)) iP |- _ => have [? ?]:= in_iP_unique H1 H2; subst; clear H1 H2 end.
Ltac unify_igotos := match goal with | H1 : In (?i, (?n1, ?X1, ?Y1)) igotos, H2 : In (?i, (?n2, ?X2, ?Y2)) igotos |- _ => have [? [? ?]] := in_igotos_unique H1 H2; subst; clear H1 H2 | H1 : In (?i1, (?n, ?X, ?Y)) igotos, H2 : In (?i2, (?n, ?X, ?Y)) igotos |- _ => have ? := in_igotos_unique_index H1 H2; subst; clear H1 H2 end.
Ltac unify_app := match goal with | H : ?l ++ ?l1 = ?l ++ ?l2 |- _ => move /app_inv_head in H; subst | H : ?a :: ?l1 = ?a :: ?l2 |- _ => (have ? : l1 = l2 by congruence); subst; clear H | H : §0^?n ++ (§1 :: ?v1) = §0^?m ++ (§1 :: ?v2) |- _ => have ? := zero_prefix_eq H; subst | H1 : §0^G ++ ?v1 = §0^?n ++ (§1 :: ?v2), H2 : ?n < G |- _ => have ? := contradict_G_prefix H1 H2; clear H1 H2 | H1 : §0^?n ++ (§1 :: ?v2) = §0^G ++ ?v1, H2 : ?n < G |- _ => have ? := contradict_G_prefix (esym H1) H2; clear H1 H2 end.
Definition cm_start : CM.Config := {| CM.state := 0; CM.value := 1 |}.
Definition bound_reachable_n (C N: nat) : Prop := forall m l r, m <= C -> reachable_n N (repeat §0 m ++ [§1] ++ r, [§1] ++ l, '?|) ([§1] ++ l, repeat §0 m ++ [§1] ++ r, '+|).
Definition goto_time (C N: nat) := (C+1)*(N+3).
Arguments first_goto_1 {C N} _ T {l r T' n X Y c Z}.
Definition increase_time (C N: nat) := (C+G+2)*(2*(goto_time C N)+3).
Arguments do_increase {C N} _ l r {i j n} k m.
Definition step_time (C N: nat) := goto_time C N + increase_time C N + 1.
Section Reflection.
Variable NM : nat.
Variable NM_spec : SM.bounded M NM.
End Reflection.
Section Transport.
Variable NP : nat.
Variable NP_spec : CM.halting P (Nat.iter NP (CM.step P) cm_start).
Definition cm_end := Nat.iter NP (CM.step P) cm_start.
Definition CP : nat := CM.value cm_end.
Definition TP : nat := sval (bound_reachable_n_CP).
Definition HTP : bound_reachable_n CP TP := svalP (bound_reachable_n_CP).
Local Definition maybe_reachable := maybe_reachable M.
Definition maybe_goto_1_time := (goto_time CP TP + NP * step_time CP TP + 2).
Definition maybe_index_try_stop_time := (NP * step_time CP TP + 2*maybe_goto_1_time + 1 + ((G + CP + 2) * (2 * goto_time CP TP + 3))).
Arguments maybe_first_goto_1 T {l r T' n X Y c Z}.
Definition maybe_increase_time := ((G + CP + 2) * (2 * maybe_goto_1_time + 3)).
Arguments maybe_increase l r {i j n} k m.
Definition maybe_index_try_step_time := 2*maybe_goto_1_time + maybe_increase_time +2.
Definition maybe_index_try_futile_time := maybe_index_try_stop_time + 3.
Definition maybe_bounded_try_time := TP + maybe_index_try_stop_time + 1.
Definition maybe_index_yes_futile_time := 2*maybe_goto_1_time + maybe_increase_time + maybe_index_try_stop_time + 5.
Definition maybe_increase_no_grow_time := maybe_goto_1_time + maybe_index_try_stop_time + 3.
Definition maybe_index_yes_grow_time := maybe_index_yes_futile_time + maybe_increase_time + 3 * maybe_goto_1_time + maybe_index_try_stop_time + 4.
Definition maybe_index_try_grow_time := maybe_index_try_futile_time + (length P) * maybe_index_try_step_time + maybe_index_yes_grow_time + maybe_goto_1_time + 1.
Definition maybe_increase_yes_grow_time := maybe_index_try_grow_time + maybe_index_yes_futile_time + 2.
Definition maybe_index_no_grow_time := maybe_index_try_grow_time + maybe_goto_1_time + maybe_index_try_stop_time + 3.
Definition maybe_bounded_try_grow_time := maybe_bounded_try_time+1.
Definition maybe_basic_state_grow_time := maybe_index_try_stop_time + 2 + maybe_bounded_try_grow_time + maybe_index_try_grow_time + maybe_index_yes_grow_time + maybe_index_no_grow_time + maybe_increase_yes_grow_time + maybe_increase_no_grow_time.
Definition maybe_goto_1_grow_time := maybe_basic_state_grow_time + maybe_goto_1_time.
Definition uniform_termination_time := ((G + (CP + 1)) * maybe_goto_1_grow_time) + (NP * step_time CP TP + 2) + maybe_basic_state_grow_time.
Local Definition clos_rt_rt1n_iff := @clos_rt_rt1n_iff (@SM.Config State Symbol).
End Transport.
End Reduction.

Lemma do_cm_step {C N: nat} : bound_reachable_n C N -> forall l r p, CM.value (CM1.step P p) <= G + C -> reachable_n (step_time C N) ([§1] ++ l, §0^(CM.value p) ++ [§1] ++ (§0^(CM.value (CM1.step P p) - CM.value p)) ++ r, '#?(CM.state p)) ([§1] ++ l, §0^(CM.value (CM1.step P p)) ++ [§1] ++ r, '#?(CM.state (CM1.step P p))).
Proof using capped_P.
move=> HN l r [i [|c]] /= HpC; first by apply: reach_refl.
move H: (nth_error P i) HpC => oi.
case: oi H; first last.
{
move=> _ _ /=.
rewrite ?nat_norm ?app_norm.
by apply: reach_refl.
}
move=> [j n] /nth_error_Some_In_iP.
rewrite /step_time.
move Hm: (S c mod (n + 1)) => m.
move: m Hm => [|m] Hcn /= Hijn.
-
have := mod_frac_lt Hcn.
move Hd: (S c * (n + 2) / (n + 1)) => d Hcd HC.
apply: (first_step (index_try_spec (i, (j, n))) l (§0^c ++ [§1] ++ §0^(d - S c) ++ r)); [ by lia | by auto with M | by rewrite ?app_norm | ].
rewrite ?app_norm.
apply: (first_goto_1 HN (increase_time C N)); [ by eauto with M | by lia | by lia |].
rewrite Hcn.
have ? := divides_frac_diff Hcn.
have := do_increase HN r ([§1] ++ l) (d - S c) 0 Hijn ltac:(lia).
apply: (reachable_n_trans' 1); [ by rewrite /increase_time; nia | by rewrite ?app_norm; do 4 f_equal; lia |].
apply: (first_step (index_yes_spec_1 (i, (j, n))) (§0^((d - S c) * (2 + n)) ++ [§1] ++ r) l); [ by lia | by auto with M | by rewrite ?app_norm | ].
apply: reachable_n_refl'.
rewrite ?app_norm.
by do 4 f_equal; lia.
-
move=> ?.
apply: (first_step (index_try_spec (i, (j, n))) l (§0^c ++ [§1] ++ r)); [by lia | by auto with M | by rewrite ?app_norm ?nat_norm | ].
rewrite ?app_norm.
apply: (first_goto_1 HN (increase_time C N)); [ by eauto with M | by lia | by lia | rewrite Hcn /increase_time ].
apply: (first_step (index_no_spec (i, (j, n))) ([§1] ++ r) (§0^c ++ [§1] ++ l)); [ by lia | by auto with M | done |].
rewrite ?app_norm.
Admitted.

Lemma iter_cm_step {C N: nat} : bound_reachable_n C N -> forall l r n, let p := (Nat.iter n (CM1.step P) cm_start) in CM.value p <= G + C -> reachable_n (n * (step_time C N)) ([§1] ++ l, [§0] ++ [§1] ++ (§0^(CM.value p - 1)) ++ r, '#?0) ([§1] ++ l, §0^(CM.value p) ++ [§1] ++ r, '#?(CM.state p)).
Proof using capped_P.
move=> HN l r n.
elim: n l r => [l r _ _ | n] /=; first by apply: reach_refl.
have := CM_facts.run_value_monotone P cm_start n.
set p := (Nat.iter n (CM1.step P) cm_start) => Hp IH l r ?.
rewrite /cm_start /= in Hp.
have ? : CM.value p <= CM.value (CM1.step P p) by apply: CM_facts.step_value_monotone.
have := IH l (§0^(CM.value (CM1.step P p) - CM.value p) ++ r) ltac:(lia).
apply: (reachable_n_trans' (step_time C N)); [by lia | by rewrite ?app_norm; do 6 f_equal; lia |].
Admitted.

Lemma search_bound (C n: nat) : C <= CM.value (Nat.iter n (CM1.step P) cm_start) -> {N | bound_reachable_n C N}.
Proof using capped_P.
elim: C.
{
rewrite /bound_reachable_n.
move=> _.
exists 1.
move=> m l r ?.
have ->: m = 0 by lia.
apply: (first_step bound_try_spec_1 r l); [by lia | by auto with M | by rewrite ?app_norm | by apply: reach_refl ].
}
move=> C IH HC.
have [N HN] := IH ltac:(lia).
exists (n * step_time C N + increase_time C N + 3 * goto_time C N + 3).
rewrite /bound_reachable_n.
move=> [|[|m]] l r Hm.
-
apply: (first_step bound_try_spec_1 r l); [by lia | by auto with M | done | by apply: reach_refl ].
-
apply: (first_step bound_try_spec_01 r l); [by lia | by auto with M | done | by apply: reach_refl ].
-
apply: (first_step bound_try_spec_00 (§0^m ++ [§1] ++ r) l); [by lia | by auto with M | by rewrite ?app_norm | ].
have [n' [?]] := transition_le_gt (fun n => CM.value (Nat.iter n (CM1.step P) cm_start)) (S m) 0 n ltac:(lia) ltac:(rewrite /cm_start /=; lia) ltac:(lia).
have := CM_facts.run_value_monotone P cm_start n'.
set p' := (Nat.iter n' (CM1.step P) cm_start).
have -> : Nat.iter (1 + n') (CM1.step P) cm_start = CM1.step P p' by done.
move=> H1p' [? ?].
rewrite /cm_start /= in H1p'.
have := iter_cm_step HN l (§0^(m - (CM.value p' - 1)) ++ [§1] ++ r) n'.
rewrite -/p'.
move /(_ ltac:(lia)).
apply: (reachable_n_trans' (increase_time C N + 3 * goto_time C N + 2)); [by nia | by rewrite ?app_norm; do 6 f_equal; lia |].
have Hp' : CM.value p' < CM.value (CM.step P p') by lia.
have [[p'j p'n] [/nth_error_Some_In_iP Hp'iP] /= Hp'n] := CM_facts.inc_value_mod Hp'.
apply: (first_step (index_try_spec (CM.state p', (p'j, p'n))) l (§0^(CM.value p' - 1) ++ [§1] ++ §0^(m - (CM.value p' - 1)) ++ [§1] ++ r)); [by lia | by auto with M | by rewrite ?app_norm; do 4 f_equal; lia |].
rewrite ?app_norm.
have ->: (1 + (CM.value p' - 1)) = CM.value p' by lia.
apply: (first_goto_1 HN (increase_time C N + 2 * goto_time C N + 1)); [ by eauto with M | by lia | by lia | ].
set k := (m - (CM.value p' - 1)).
have ?: (k + 1) * (1 + p'n) <= CM.value p'.
{
suff: (CM.value (CM1.step P p') - CM.value p') * (1 + p'n) = CM.value p' by nia.
suff: CM.value (CM1.step P p') = (CM.value p') * (p'n + 2) / (p'n + 1).
{
move=> ->.
by have := divides_frac_diff Hp'n.
}
rewrite /CM1.step.
have {1}->: CM1.value p' = S (CM1.value p' - 1) by lia.
move: Hp'iP => /nth_error_Some_In_iP ->.
by rewrite Hp'n.
}
have -> : CM.value p' = (k+1)*(1+p'n)+(CM.value p' - (k+1)*(1+p'n)) by lia.
move: (Hp'iP) => /(fail_increase HN r (§0^(CM.value p' - (k + 1) * (1 + p'n)) ++ [§1] ++ l)) => /(_ k).
have ? := iP_capped Hp'iP.
have ? : 4 <= G by (rewrite /G; lia).
have ? : (k + 1) * (2 + p'n) - (G + 1) <= C by lia.
move /(_ ltac:(lia)).
apply: (reachable_n_trans' (2 * goto_time C N + 1)); first by lia.
{
rewrite ?app_norm.
have ->: ((k + 1) * (1 + p'n) + (CM.value p' - (k + 1) * (1 + p'n))) = CM.value p' by lia.
by rewrite Hp'n.
}
apply: (first_goto_1 HN (goto_time C N + 1)); [ by eauto with M | by lia | by lia |].
apply: (first_step (increase_no_spec (CM.state p', (p'j, p'n))) (§0^(CM.value p' - (k + 1) * (1 + p'n)) ++ [§1] ++ l) (§0^((k + 1) * (1 + p'n) + k) ++ [§1] ++ r)); [by lia | by auto with M | done | ].
apply: (first_goto_1 HN 0); [by eauto with M | by move: ((k + 1) * (1 + p'n)); lia | by lia |].
apply: reachable_n_refl'.
rewrite ?app_norm ?nat_norm.
do 4 f_equal.
Admitted.

Theorem bounded_M_to_terminating_P : CM.halting P (Nat.iter NM (CM.step P) cm_start).
Proof using NM NM_spec capped_P.
rewrite /CM.halting.
move HNM: (Nat.iter NM (CM.step P) cm_start) => cm_end.
have : CM.step P cm_end = cm_end \/ CM.step P cm_end <> cm_end by do 2 (decide equality).
case; first done.
move=> He.
exfalso.
have /CM_facts.acyclicity : not (CM.halting P (Nat.iter NM (CM.step P) cm_start)) by rewrite HNM.
set f := (fun i : nat => Nat.iter i (CM1.step P) cm_start).
rewrite seq_last map_app.
move /(@NoDup_remove CM1.Config) => [+ _].
rewrite app_nil_r.
have [L [H1L H2L]] := NM_spec ([§1], [§0] ++ [§1] ++ §0^(CM.value cm_end - 1), '#?0).
set g : _ -> SM.Config := (fun X => ([§1], §0^(CM.value X) ++ [§1] ++ §0^(CM.value cm_end - (CM.value X)), '#? (CM.state X))).
move /(NoDup_map (f := g)).
apply: unnest.
{
move=> [p1 v1] [p2 v2].
rewrite /g /=.
by move=> [] /zero_prefix_eq => -> ->.
}
set L' := (map g (map f (seq 0 (1 + NM)))).
move=> HL'.
have /(NoDup_incl_length HL') : incl L' L.
{
move=> x + /ltac:(apply: H1L).
rewrite /L' in_map_iff.
move=> [X] [<-].
rewrite in_map_iff.
move=> [i] [<-].
rewrite in_seq.
move=> [_ ?].
rewrite /f /g.
have [N HN] := search_bound (CM.value cm_end) NM ltac:(rewrite HNM; lia).
have := CM_facts.run_value_monotone P cm_start i.
set Y := (Nat.iter i (CM1.step P) cm_start).
have ? : CM.value Y <= CM.value cm_end.
{
rewrite /Y -HNM.
apply: CM_facts.value_monotone.
by lia.
}
move=> H1Y.
rewrite /cm_start /= in H1Y.
have /= := iter_cm_step HN [] (§0^(CM.value cm_end - CM.value Y)) i.
rewrite -/Y ?app_norm.
move /(_ ltac:(lia)) /reachable_n_reachable.
congr (SM.reachable).
do 5 f_equal.
by lia.
}
rewrite /L' ?map_length seq_length.
Admitted.

Lemma bound_reachable_n_CP : {N | bound_reachable_n CP N}.
Proof using capped_P.
apply: (search_bound _ NP).
rewrite /CP /cm_end.
Admitted.

Lemma CP_pos : 1 <= CP.
Proof.
have ->: 1 = CM.value cm_start by done.
Admitted.

Lemma large_index_terminal {p i l r} : length P <= i -> terminal M (l, r, (basic_state (index p i))).
Proof.
Admitted.

Lemma large_increase_terminal {p i l r} : length P <= i -> terminal M (l, r, (basic_state (increase p i))).
Proof.
Admitted.

Lemma index_try_step_shape {y l r i} : SMX.step M (l, r, '#? i) y -> (l = [§1] ++ skipn 1 l) /\ (r = [§0] ++ skipn 1 r).
Proof.
Admitted.

Lemma index_yes_step_shape {y l r i j n} : In (i, (j, n)) iP -> SMX.step M (l, r, '#+ i) y -> (r = [§1] ++ skipn 1 r) \/ (r = §0^(1+n) ++ skipn (n+1) r).
Proof.
move=> H1i /stepE [] > [] *; subst; try done.
-
by left.
-
right.
move Hn': (n' in §0^(1 + n') ++ _) => n'.
have [_ <-] := in_iP_unique (n := n) (n' := n') ltac:(eassumption) ltac:(subst; eassumption).
rewrite skipn_app repeat_length (_ : n + 1 - (1 + n) = 0); first by lia.
Admitted.

Lemma index_no_step_shape {y l r i} : SMX.step M (l, r, '#-i) y -> (r = [§0] ++ skipn 1 r).
Proof.
Admitted.

Lemma increase_try_step_shape {y l r i} : SMX.step M (l, r, '$?i) y -> (l = [§1] ++ [§0] ++ skipn 2 l) \/ (l = [§1] ++ [§1] ++ skipn 2 l).
Proof.
Admitted.

Lemma increase_yes_step_shape {y l r i} : SMX.step M (l, r, '$+i) y -> (l = [§1] ++ skipn 1 l).
Proof.
Admitted.

Lemma increase_no_step_shape {y l r i} : SMX.step M (l, r, '$-i) y -> (l = [§1] ++ skipn 1 l).
Proof.
Admitted.

Lemma bound_try_step_shape {y l r} : SMX.step M (l, r, '?|) y -> ((l = [§1] ++ skipn 1 l) \/ (l = [§0] ++ [§1] ++ skipn 2 l) \/ (l = [§0] ++ [§0] ++ skipn 2 l)) /\ (r = [§1] ++ skipn 1 r).
Proof.
Admitted.

Lemma universal_maybe_reachable_terminal {x T} : (forall z, maybe_reachable T x z) -> exists y, reachable_n T x y /\ terminal M y.
Proof.
move=> /(_ ([], [], '?|)).
case; last done.
move=> ?.
eexists.
constructor; first by eassumption.
Admitted.

Lemma not_in_gotos_terminal l r n X Y : not (In (n, X, Y) gotos) -> terminal M (l, r, goto n X Y).
Proof.
Admitted.

Lemma maybe_index_try_run l r z : maybe_reachable (NP * step_time CP TP) ([§1] ++ l, [§0] ++ [§1] ++ §0^(CP-1) ++ r, '#?0) z.
Proof using NP_spec.
right.
have := iter_cm_step HTP l r NP.
rewrite -/cm_end /= -/CP.
move /(_ ltac:(lia)) => ?.
eexists.
constructor; first by eassumption.
apply: large_index_terminal.
suff : not (CM.state cm_end < length P) by lia.
move /CM_facts.step_progress => /(_ CP_pos).
move: (NP_spec).
rewrite -/cm_end /CM.halting.
move=> -> [|]; last by lia.
move /(f_equal CM.state) => /=.
Admitted.

Lemma maybe_goto_1_far {l r m n X Y z T} : (NP * step_time CP TP + 2) <= T -> G + (CP+1) <= m -> maybe_reachable T (l, §0^m ++ r, goto n X Y) z.
Proof using NP_spec.
move=> ? ?.
suff: maybe_reachable (NP * step_time CP TP + 2) (l, §0^(G + (CP+1)) ++ §0^(m-(G + (CP + 1))) ++ r, goto n X Y) z.
{
apply maybe_reachable_mon'; first by lia.
rewrite ?app_norm.
do 5 f_equal.
by lia.
}
have := in_dec _ (n, X, Y) gotos.
move=> /(_ ltac:(do 4 (decide equality))) [/gotos_igotos [i ?]| ?]; first last.
{
apply: terminal_maybe_reachable.
by apply: not_in_gotos_terminal.
}
apply: (maybe_first_step (goto_spec_G (i, (n, X, Y))) l (§0^(CP + 1) ++ §0^(m-(G + (CP + 1))) ++ r)); [by lia | by auto with M | by rewrite ?app_norm |].
have ? := CP_pos.
apply: (maybe_first_step bound_try_spec_00 (§0^(CP - 1 + (m - (G + (CP + 1)))) ++ r) (§0^i ++ [§1] ++ §0^(G - 2 - i) ++ l)); [by lia | by auto with M | rewrite ?app_norm; do 4 f_equal; lia |].
have := maybe_index_try_run ((§0^i ++ [§1] ++ §0^(G - 2 - i)) ++ l) (§0^(m - (G + (CP + 1))) ++ r) z.
Admitted.

Lemma maybe_goto_1 l r n X Y m : maybe_reachable maybe_goto_1_time (l, §0^m ++ [§1] ++ r, goto n X Y) ([§1] ++ r, §0^m ++ l, basic_state (if m mod (n+1) is 0 then X else Y)).
Proof using NP_spec.
rewrite /maybe_goto_1_time.
have := in_dec _ (n, X, Y) gotos.
move=> /(_ ltac:(do 4 decide equality)) [| ?]; first last.
{
apply: terminal_maybe_reachable.
by apply: not_in_gotos_terminal.
}
have [? | ?]: m <= G + CP \/ G + CP < m by lia.
{
move=> /gotos_igotos => [[i]] /(goto_1 HTP l r) => /(_ m ltac:(lia)) /reachable_n_maybe_reachable.
apply: maybe_reachable_mon'; [by lia | done].
}
move=> ?.
Admitted.

Lemma maybe_index_try_stop l m z T : maybe_index_try_stop_time <= T -> maybe_reachable T ([§1] ++ l, §0^1 ++ [§1] ++ §0^m, '#?0) z.
Proof using NP_spec.
move /maybe_reachable_mon'.
apply; first by reflexivity.
rewrite /maybe_index_try_stop_time.
have [? | Hm]: CP - 1 <= m \/ m < CP - 1 by lia.
{
have := maybe_index_try_run l (§0^(m - (CP - 1))) z.
apply: maybe_reachable_mon'; [by nia | by rewrite ?app_norm; do 6 f_equal; lia ].
}
set T' := ((G + CP + 2) * (2 * goto_time CP TP + 3)).
have [n [?]] := transition_le_gt (fun n => CM.value (Nat.iter n (CM1.step P) cm_start)) (m + 1) 0 NP ltac:(lia) ltac:(rewrite /cm_start /=; lia) ltac:(rewrite /cm_end -/CP; lia).
have := CM_facts.run_value_monotone P cm_start n.
set p := (Nat.iter n (CM1.step P) cm_start).
have -> : Nat.iter (1 + n) (CM1.step P) cm_start = CM1.step P p by done.
move=> H1p [? ?].
rewrite /cm_start /= in H1p.
have := iter_cm_step HTP l (§0^(m - (CM.value p - 1))) n.
rewrite -/p.
move=> /(_ ltac:(lia)) /reachable_n_maybe_reachable.
apply: (maybe_reachable_trans' (2*maybe_goto_1_time + 1 + T')); [ by nia | rewrite ?app_norm; do 6 f_equal; by lia | ].
have Hp : CM.value p < CM.value (CM.step P p) by lia.
have [[pj pn] [/nth_error_Some_In_iP HpiP] /= Hpn] := CM_facts.inc_value_mod Hp.
apply: (maybe_first_step (index_try_spec (CM.state p, (pj, pn))) l (§0^(CM.value p - 1) ++ [§1] ++ §0^(m - (CM.value p - 1)))); [by nia | by auto with M | by rewrite ?app_norm; do 4 f_equal; lia |].
rewrite ?app_norm.
have ->: (1 + (CM.value p - 1)) = CM.value p by lia.
apply: (maybe_first_goto_1 (maybe_goto_1_time + T')); [by lia | rewrite Hpn].
set k := (m - (CM.value p - 1)).
have ?: (k + 1) * (1 + pn) <= CM.value p.
{
suff: (CM.value (CM1.step P p) - CM.value p) * (1 + pn) = CM.value p by nia.
suff: CM.value (CM1.step P p) = (CM.value p) * (pn + 2) / (pn + 1).
{
move=> ->.
by have := divides_frac_diff Hpn.
}
rewrite /CM1.step.
have {1}->: CM1.value p = S (CM1.value p - 1) by lia.
move: HpiP => /nth_error_Some_In_iP ->.
by rewrite Hpn.
}
have -> : CM.value p = (k+1)*(1+pn)+(CM.value p - (k+1)*(1+pn)) by lia.
have := do_increase HTP [] (§0^((1 + pn) + (CM.value p - (k + 1) * (1 + pn))) ++ [§1] ++ l) k 0 HpiP ltac:(lia).
move /reachable_n_maybe_reachable.
apply: (maybe_reachable_trans' (maybe_goto_1_time + goto_time CP TP + 1)); first by nia.
{
rewrite ?app_norm.
do 4 f_equal.
by lia.
}
apply: (maybe_first_step (index_yes_spec_n1 (CM1.state p, (pj, pn))) (§0^(k * (2 + pn)) ++ [§1]) (§0^(CM.value p - (k + 1) * (1 + pn)) ++ [§1] ++ l)); [by lia | by auto with M | by rewrite ?app_norm; do 4 f_equal; lia |].
rewrite ?app_norm.
apply: (maybe_first_goto_1 0); first by lia.
rewrite ?app_norm.
right.
eexists.
constructor; first by apply: reach_refl.
Admitted.

Lemma maybe_goto_1_futile {T l n X Y m z} : maybe_index_try_stop_time + 2 <= T -> maybe_reachable T (l, §0^m, goto n X Y) z.
Proof using NP_spec.
move=> ?.
suff: maybe_reachable (maybe_index_try_stop_time + 2) (l, §0^m, goto n X Y) z by apply: maybe_reachable_mon'.
rewrite /maybe_index_try_stop_time.
have /(_ ltac:(do 4 decide equality)) [HnXY | /not_in_gotos_terminal ?] := in_dec _ (n, X, Y) gotos; last by apply: terminal_maybe_reachable.
have [? | ?]: G+CP+1 <= m \/ m <= G+CP by lia.
{
have := @maybe_goto_1_far l [] m.
rewrite ?app_norm.
apply; by lia.
}
have [? | ?]: m < G \/ G <= m by lia.
{
right.
exists (l, §0^m, goto n X Y).
constructor; first by apply: reach_refl.
move=> y /stepE [] > []; try done.
-
move=> ? /(f_equal (@length Symbol)).
rewrite ?app_length ?repeat_length.
by lia.
-
move=> ? Hm.
exfalso.
have : not (In §1 (§0^m)) by move /(@repeat_spec Symbol).
apply.
rewrite Hm ?in_app_iff.
clear.
by firstorder done.
}
move: (HnXY) => /gotos_igotos => [[i ?]].
apply: (maybe_first_step (goto_spec_G (i, (n, X, Y))) l (§0^(m - G))); [by lia | by auto with M | by rewrite ?app_norm; do 4 f_equal; lia |].
have [? | ?] : m - G < 2 \/ 2 <= m - G by lia.
{
right.
eexists.
constructor; first by apply: reach_refl.
move=> ? /bound_try_step_shape.
have : m - G = 0 \/ m - G = 1 by lia.
move=> [-> | ->]; clear; by firstorder done.
}
apply: (maybe_first_step bound_try_spec_00 (§0^(m - G - 2)) (§0^i ++ [§1] ++ §0^(G - 2 - i) ++ l)); [by lia | by auto with M | by rewrite ?app_norm; do 3 f_equal; lia |].
rewrite ?app_norm.
apply: maybe_index_try_stop.
rewrite /maybe_index_try_stop_time.
Admitted.

Lemma maybe_increase l r i j n k m : In (i, (j, n)) iP -> maybe_reachable maybe_increase_time (§0^m ++ [§1] ++ §0^k ++ l, §0^(k * (1+n)) ++ r, '#+i) (§0^(m + k * (2+n)) ++ [§1] ++ l, r, '#+i).
Proof using NP_spec.
rewrite /maybe_increase_time.
move=> Hijn.
move: l r k m.
have H : forall k m l r, maybe_reachable ((k+1)*(2 * maybe_goto_1_time + 3)) (§0^m ++ [§1] ++ §0^k ++ l, §0^(k * (1+n)) ++ r, '#+i) (§0^(m + k * (2+n)) ++ [§1] ++ l, r, '#+i).
{
elim.
{
move=> m l r.
rewrite ?app_norm ?nat_norm.
by apply: maybe_reachable_refl'.
}
move=> k IH m l r.
have ? := iP_capped Hijn.
pose N' := (k+1)*(2 * maybe_goto_1_time + 3).
apply: (maybe_first_step (index_yes_spec_n1 (i, (j, n))) (§0^m ++ [§1] ++ §0^(1+k) ++ l) (§0^(k * (1 + n)) ++ r)); [by lia | by auto with M | by rewrite ?app_norm |].
rewrite ?app_norm.
apply: (maybe_first_goto_1 (N' + maybe_goto_1_time + 2)); first by lia.
apply: (maybe_first_step (increase_try_spec_0 (i, (j, n))) (§0^k ++ l) (§0^(n + m) ++ [§1] ++ §0^(k * (1 + n)) ++ r)); [by lia | by auto with M | by rewrite ?app_norm |].
rewrite ?app_norm.
apply: (maybe_first_goto_1 (N' + 1)); first by lia.
apply: (maybe_first_step (increase_yes_spec (i, (j, n))) (§0^(k * (1 + n)) ++ r) (§0^(1 + (n + m)) ++ [§1] ++ §0^k ++ l)); [by lia | by auto with M | by rewrite ?app_norm |].
have := IH (m + n + 2) l r.
apply: maybe_reachable_mon'; first by lia.
rewrite ?app_norm.
by do 5 f_equal; lia.
}
move=> l r k m.
have [? | ?] : k <= G + CP \/ G + CP < k by lia.
{
have := H k m l r.
by apply: maybe_reachable_mon'; first by nia.
}
pose k' := G + CP.
have := H k' m (§0^(k-k') ++ l) (§0^((k-k') * (1 + n)) ++ r).
apply: (maybe_reachable_trans' (maybe_goto_1_time + 1)); first by lia.
{
rewrite ?app_norm.
(do 4 f_equal); last by lia.
do 2 f_equal.
by lia.
}
apply: (maybe_first_step (index_yes_spec_n1 (i, (j, n))) (§0^(m + k' * (2 + n)) ++ [§1] ++ §0^(k - k') ++ l) (§0^((k - k' - 1) * (1 + n)) ++ r)); [ by lia | by auto with M | by rewrite ?app_norm; do 4 f_equal; nia | ].
rewrite ?app_norm /k'.
have ? := CP_pos.
rewrite /maybe_goto_1_time.
Admitted.

Lemma maybe_increase_next l r i j n c k m : In (i, (j, n)) iP -> c / (1+n) <= k -> maybe_reachable (maybe_increase_time+1) (§0^m ++ [§1] ++ §0^k ++ l, §0^c ++ [§1] ++ r, '#+i) ([§1] ++ r, §0^(m + c + (c / (1+n)) + (c mod (1+n))) ++ [§1] ++ §0^(k - (c / (1+n))) ++ l, '#?j).
Proof using NP_spec.
have := Nat.div_mod c (1+n) ltac:(lia).
move: (c / (1+n)) => k'.
have ->: (1 + n) * k' = k' * (1 + n) by lia.
move=> ? Hijn ?.
have := maybe_increase (§0^(k-k') ++ l) (§0^(c mod (1 + n)) ++ [§1] ++ r) k' m Hijn.
apply: (maybe_reachable_trans' 1); first by lia.
{
rewrite ?app_norm.
do 4 f_equal; last by lia.
do 2 f_equal.
by lia.
}
have ? := Nat.mod_upper_bound c (1+n) ltac:(lia).
have [Hc | Hc]: c mod (1 + n) = 0 \/ c mod (1 + n) = 1 + (c mod (1 + n) - 1) by lia.
{
rewrite Hc.
apply: (maybe_first_step (index_yes_spec_1 (i, (j, n))) (§0^(m + k' * (2 + n)) ++ [§1] ++ §0^(k - k') ++ l) r); [ by lia | by auto with M | done | ].
apply: maybe_reachable_refl'.
rewrite ?nat_norm ?app_norm.
do 4 f_equal.
by lia.
}
rewrite Hc.
apply: terminal_maybe_reachable.
Admitted.

Lemma maybe_increase_stop r i j n c k m z : In (i, (j, n)) iP -> k < c / (1+n) -> maybe_reachable (maybe_increase_time+ maybe_goto_1_time + 1) (§0^m ++ [§1] ++ §0^k, §0^c ++ [§1] ++ r, '#+i) z.
Proof using NP_spec.
have := Nat.div_mod c (1+n) ltac:(lia).
move: (c / (1 + n)) => k'.
move: (c mod (1 + n)) => k'' -> Hijn ?.
have := maybe_increase [] (§0^((1 + n) * (k'-k) + k'') ++ [§1] ++ r) k m Hijn.
apply: (maybe_reachable_trans' (maybe_goto_1_time + 1)); first by lia.
{
rewrite ?app_norm.
do 4 f_equal.
by lia.
}
move: ((m + k * (2 + n))) => {}m.
apply: (maybe_first_step (index_yes_spec_n1 (i, (j, n))) (§0^m ++ [§1]) (§0^((1 + n) * (k' - k - 1) + k'') ++ [§1] ++ r)); [ by lia | by auto with M | by rewrite ?app_norm; do 4 f_equal; nia |].
rewrite ?app_norm.
apply: (maybe_first_goto_1 0); first by lia.
Admitted.

Lemma maybe_increase_fail l r i j n c k m : In (i, (j, n)) iP -> k < c / (1+n) -> maybe_reachable (maybe_increase_time + 3*maybe_goto_1_time + 3) (§0^m ++ [§1] ++ §0^k ++ [§1] ++ l, §0^c ++ [§1] ++ r, '#+i) ([§1] ++ r, §0^(c+m+k+1) ++ [§1] ++ l, '+|).
Proof using NP_spec.
have := Nat.div_mod c (1+n) ltac:(lia).
move: (c / (1 + n)) => k'.
move: (c mod (1 + n)) => k'' -> Hijn ?.
have := maybe_increase ([§1] ++ l) (§0^((1 + n) * (k'-k) + k'') ++ [§1] ++ r) k m Hijn.
apply: (maybe_reachable_trans' (3*maybe_goto_1_time + 3)); first by lia.
{
rewrite ?app_norm.
do 4 f_equal.
by lia.
}
apply: (maybe_first_step (index_yes_spec_n1 (i, (j, n))) (§0^((m + k * (2 + n))) ++ [§1] ++ [§1] ++ l) (§0^((1 + n) * (k' - k - 1) + k'') ++ [§1] ++ r)); [ by lia | by auto with M | by rewrite ?app_norm; do 4 f_equal; nia |].
rewrite ?app_norm.
apply: (maybe_first_goto_1 (2*maybe_goto_1_time + 2)); first by lia.
apply: (maybe_first_step (increase_try_spec_1 (i, (j, n)))); [by lia | by auto with M | by rewrite ?app_norm; reflexivity |].
rewrite ?app_norm.
apply: (maybe_first_goto_1 (maybe_goto_1_time + 1)); first by lia.
apply: (maybe_first_step (increase_no_spec (i, (j, n)))); [ by lia | by auto with M | by rewrite ?app_norm; reflexivity |].
rewrite ?app_norm.
apply: (maybe_first_goto_1 0); first by lia.
apply: maybe_reachable_refl'.
rewrite ?app_norm.
do 4 f_equal.
Admitted.

Lemma maybe_index_try_step l r p : maybe_reachable maybe_index_try_step_time ([§1] ++ l, §0^(CM.value p) ++ [§1] ++ §0^(CM.value (CM1.step P p) - CM.value p) ++ r, '#?(CM.state p)) ([§1] ++ l, §0^(CM.value (CM1.step P p)) ++ [§1] ++ r, '#?(CM.state (CM1.step P p))).
Proof using NP_spec.
rewrite /maybe_index_try_step_time.
move: p => [i [|c]] /=.
{
by apply: maybe_reachable_refl'.
}
move H: (nth_error P i) => oi.
case: oi H; first last.
{
move=> _ /=.
rewrite ?nat_norm ?app_norm.
by apply: maybe_reachable_refl'.
}
move=> [j n] /nth_error_Some_In_iP /=.
move Hm: (S c mod (n + 1)) => m.
move: m Hm => [|m] Hcn /= Hijn.
-
have := mod_frac_lt Hcn.
move Hd: (S c * (n + 2) / (n + 1)) => d Hcd.
apply: (maybe_first_step (index_try_spec (i, (j, n))) l (§0^c ++ [§1] ++ §0^(d - S c) ++ r)); [ by lia | by auto with M | by rewrite ?app_norm | ].
rewrite ?app_norm.
apply: (maybe_first_goto_1 (maybe_goto_1_time + maybe_increase_time + 1)); first by lia.
rewrite Hcn.
have ? : (d - S c) * (1 + n) = S c.
{
rewrite -Hd.
by apply: divides_frac_diff.
}
have := maybe_increase r ([§1] ++ l) (d - S c) 0 Hijn.
apply: (maybe_reachable_trans' (maybe_goto_1_time + 1)); first by lia.
{
rewrite ?app_norm.
do 4 f_equal.
by lia.
}
apply: (maybe_first_step (index_yes_spec_1 (i, (j, n)))); [by lia | by auto with M | by rewrite ?app_norm; reflexivity | ].
apply: maybe_reachable_refl'.
rewrite ?app_norm.
do 4 f_equal.
by lia.
-
apply: (maybe_first_step (index_try_spec (i, (j, n))) l (§0^c ++ [§1] ++ r)); [by lia | by auto with M | by rewrite ?app_norm ?nat_norm | ].
rewrite ?app_norm.
apply: (maybe_first_goto_1 (maybe_goto_1_time + 1)); first by lia.
rewrite Hcn.
apply: (maybe_first_step (index_no_spec (i, (j, n))) ([§1] ++ r) (§0^c ++ [§1] ++ l)); [ by lia | by auto with M | done |].
rewrite ?app_norm.
Admitted.

Lemma maybe_index_try_futile l m i z : maybe_reachable maybe_index_try_futile_time (l, §0^m, '#?i) z.
Proof using NP_spec.
rewrite /maybe_index_try_futile_time.
move: l => [|a l].
{
by apply: terminal_maybe_reachable => ? /index_try_step_shape [? ?].
}
case: a.
{
by apply: terminal_maybe_reachable => ? /index_try_step_shape [? ?].
}
have [-> | ?] : m = 0 \/ 1 <= m by lia.
{
by apply: terminal_maybe_reachable => ? /index_try_step_shape [? ?].
}
have [? | /in_iPI [j [n Hijn]]]: length P <= i \/ i < length P by lia.
{
apply: terminal_maybe_reachable.
by apply: large_index_terminal.
}
apply: (maybe_first_step (index_try_spec (i, (j, n))) l (§0^(m-1))); [ by lia | by auto with M | by rewrite ?app_norm; do 4 f_equal; lia | ].
rewrite ?app_norm.
apply: maybe_goto_1_futile.
Admitted.

Lemma maybe_bounded_try l r : maybe_reachable maybe_bounded_try_time (r, l, '?|) (l, r, '+|).
Proof using NP_spec.
rewrite /maybe_bounded_try_time.
move: l => [|a l].
{
right.
eexists.
constructor; first by apply: reach_refl.
by move=> ? /bound_try_step_shape [? ?].
}
case: a.
{
right.
eexists.
constructor; first by apply: reach_refl.
by move=> ? /bound_try_step_shape [? ?].
}
move: r => [|b r].
{
right.
eexists.
constructor; first by apply: reach_refl.
by move=> ? /bound_try_step_shape [[|[|]] ?].
}
case: b.
{
move: r=> [|b r].
{
right.
eexists.
constructor; first by apply: reach_refl.
by move=> ? /bound_try_step_shape [[|[|]] ?].
}
case: b.
{
have [[m ->]|] := list_symbol_shape r.
{
apply: (maybe_first_step bound_try_spec_00 (§0^m) l); [ by lia | by auto with M | by rewrite ?app_norm | ].
rewrite ?app_norm.
apply: maybe_index_try_stop.
by lia.
}
move=> [m [+ ->]] => {}r.
have [| ?]: m + 2 <= CP \/ CP < m + 2 by lia.
{
move /(HTP (m+2) l r) => + /ltac:(left).
apply: reachable_n_mon'; first by lia.
rewrite ?app_norm.
do 5 f_equal; by lia.
}
apply: (maybe_first_step bound_try_spec_00 (§0^m ++ [§1] ++ r) l); [ by lia | by auto with M | by rewrite ?app_norm; do 4 f_equal; lia | ].
have := maybe_index_try_run l (§0^(m - (CP - 1)) ++ [§1] ++ r) (§1 :: l, §0 :: §0 :: §0^m ++ [§1] ++ r, '+|).
apply: maybe_reachable_mon'; first by (rewrite /maybe_index_try_stop_time; nia).
rewrite ?app_norm.
do 7 f_equal.
by lia.
}
apply: (maybe_first_step bound_try_spec_01 r l); [ by lia | by auto with M | by rewrite ?app_norm |].
apply: maybe_reachable_refl'.
by rewrite ?app_norm.
}
apply: (maybe_first_step bound_try_spec_1 r l); [ by lia | by auto with M | by rewrite ?app_norm |].
apply: maybe_reachable_refl'.
Admitted.

Lemma maybe_index_yes_near_futile l m i j n z : In (i, (j, n)) iP -> m <= n -> maybe_reachable 0 (l, §0^m, '#+i) z.
Proof.
move=> Hijn ?.
apply: terminal_maybe_reachable.
move=> ? /(index_yes_step_shape Hijn).
case; first by case: (m).
move /(f_equal (@length Symbol)).
rewrite ?app_length ?repeat_length.
Admitted.

Lemma maybe_index_yes_futile l m i z : maybe_reachable maybe_index_yes_futile_time (l, §0^m, '#+i) z.
Proof using NP_spec.
rewrite /maybe_index_yes_futile_time.
have [? | /in_iPI [j [n Hijn]]] : length P <= i \/ i < length P by lia.
{
apply: terminal_maybe_reachable.
by apply: large_index_terminal.
}
have [? | ?] : m <= n \/ n < m by lia.
{
apply: (maybe_reachable_mon' (n := 0)); [by lia | by reflexivity |].
apply: maybe_index_yes_near_futile; by eassumption.
}
have [[m' ->]|]:= list_symbol_shape l.
{
apply: (maybe_first_step (index_yes_spec_n1 (i, (j, n))) (§0^m') (§0^(m-(n+1)))); [ by lia | by auto with M | by rewrite ?app_norm; do 5 f_equal; lia |].
rewrite ?app_norm.
apply: maybe_goto_1_futile.
by lia.
}
move=> [k1 [+ ->]] => {}l.
have [[k2 ->]|] := list_symbol_shape l.
{
have [| ?]: m / (1+n) <= k2 \/ k2 < m / (1+n) by lia.
{
have := Nat.div_mod m (1+n) ltac:(lia).
move Hk: (m / (1+n)) => k Hm ?.
have := maybe_increase (§0^(k2-k)) (§0^(m mod (1 + n))) k k1 Hijn.
apply: (maybe_reachable_trans' 0); first by lia.
{
rewrite ?app_norm.
do 5 f_equal; by lia.
}
apply: (maybe_reachable_mon' (n := 0)); [by lia | by reflexivity |].
move: (Hijn) => /maybe_index_yes_near_futile.
apply.
have := Nat.mod_upper_bound m (1+n) ltac:(lia).
by lia.
}
have := maybe_increase [] (§0^(m - k2 * (1+n))) k2 k1 Hijn.
apply: (maybe_reachable_trans' (maybe_goto_1_time + 1)); first by lia.
{
rewrite ?app_norm.
do 5 f_equal.
have ? := div_mul_le m (1+n) ltac:(lia).
by nia.
}
move: (m - k2 * (1 + n)).
move: (k1 + k2 * (2 + n)) => k1' m'.
have [? | ?]: m' <= n \/ n < m' by lia.
{
apply: (maybe_reachable_mon' (n := 0)); [by lia | by reflexivity |].
apply: maybe_index_yes_near_futile; by eassumption.
}
apply: (maybe_first_step (index_yes_spec_n1 (i, (j, n))) (§0^k1' ++ [§1]) (§0^(m' - (n+1)))); [ by lia | by auto with M | by rewrite ?app_norm; do 4 f_equal; lia |].
rewrite ?app_norm.
apply: (maybe_first_goto_1 0); first by lia.
by apply: terminal_maybe_reachable => ? /increase_try_step_shape [|].
}
move=> [k2 [+ ->]] => {}l.
have [| ?] : m / (1+n) <= k2 \/ k2 < m / (1+n) by lia.
{
have := Nat.div_mod m (1+n) ltac:(lia).
move Hk: (m / (1+n)) => k Hm ?.
have := maybe_increase (§0^(k2-k) ++ [§1] ++ l) (§0^(m mod (1 + n))) k k1 Hijn.
apply: (maybe_reachable_trans' 0); first by lia.
{
rewrite ?app_norm.
do 5 f_equal; last by lia.
f_equal.
by lia.
}
apply: (maybe_reachable_mon' (n := 0)); first by lia.
{
by reflexivity.
}
move: (Hijn) => /maybe_index_yes_near_futile.
apply.
have := Nat.mod_upper_bound m (1+n) ltac:(lia).
by lia.
}
have := maybe_increase ([§1] ++ l) (§0^(m - k2 * (1+n))) k2 k1 Hijn.
apply: (maybe_reachable_trans' (2*maybe_goto_1_time + maybe_index_try_stop_time + 5)); first by lia.
{
rewrite ?app_norm.
do 5 f_equal.
have ? := div_mul_le m (1+n) ltac:(lia).
by nia.
}
move: (m - k2 * (1 + n)).
move: (k1 + k2 * (2 + n)) => k1' m'.
have [? | ?]: m' <= n \/ n < m' by lia.
{
apply: (maybe_reachable_mon' (n := 0)); [by lia | by reflexivity |].
apply: maybe_index_yes_near_futile; by eassumption.
}
apply: (maybe_first_step (index_yes_spec_n1 (i, (j, n))) (§0^k1' ++ [§1] ++ [§1] ++ l) (§0^(m' - (n+1)))); [ by lia | by auto with M | by rewrite ?app_norm; do 4 f_equal; lia |].
rewrite ?app_norm.
apply: (maybe_first_goto_1 (maybe_goto_1_time + maybe_index_try_stop_time + 4)); first by lia.
apply: (maybe_first_step (increase_try_spec_1 (i, (j, n))) l (§0^(n + k1') ++ [§1] ++ §0^(m' - (n + 1)))); [ by lia | by auto with M | by rewrite ?app_norm |].
rewrite ?app_norm.
apply: (maybe_first_goto_1 (maybe_index_try_stop_time + 3)); first by lia.
apply: (maybe_first_step (increase_no_spec (i, (j, n))) (§0^(m' - (n + 1))) (§0^(1 + (n + k1')) ++ [§1] ++ l)); [ by lia | by auto with M | by rewrite ?app_norm |].
rewrite ?app_norm.
apply: maybe_goto_1_futile.
Admitted.

Lemma maybe_bounded_yes_grow l r m : exists '(l', r', n, X, Y), maybe_reachable 1 (l, §0^m ++ r, '+|) (l', §0^(m+1) ++ r', goto n X Y).
Proof using capped_P.
have := Exists_dec (fun '(i, (n, X, Y)) => l = ([§1] ++ §0^i ++ [§1] ++ §0^(G-2-i)) ++ skipn G l) igotos.
case.
{
move=> [i] [[n X] Y].
by do 2 (decide equality).
}
-
rewrite Exists_exists.
move=> [[i] [[n X] Y]] [Hi ->].
exists ((§0^(n + 1) ++ skipn G l), (§0^(G - (n + 2)) ++ r), n, X, Y).
apply: (maybe_first_step (bound_yes_spec (i, (n, X, Y))) (skipn G l) (§0^m ++ r)); [by lia | by auto with M | done |].
apply: maybe_reachable_refl'.
have ? := igotos_capped Hi.
rewrite /G ?app_norm /gotos ?app_length /=.
do 4 f_equal.
by lia.
-
move=> H.
exists ([], [], 0, +|, +|).
apply: terminal_maybe_reachable.
move=> y /stepE [] > [] *; subst; try done.
apply: H.
apply /Exists_exists.
eexists.
constructor; first by eassumption.
rewrite /= ?app_norm.
do 4 f_equal.
rewrite ?app_assoc skipn_app.
have ? := in_igotos_lt ltac:(eassumption).
set s := (skipn G _).
have -> : s = [].
{
rewrite /s skipn_all2; last done.
rewrite ?app_length ?repeat_length /= /G.
by lia.
}
rewrite ?app_length ?repeat_length /= /G.
set k := (k in skipn k _).
have -> : k = 0 by lia.
Admitted.

Lemma maybe_increase_no_grow l r m i : exists '(l', r', n, X, Y), maybe_reachable maybe_increase_no_grow_time (l, §0^m ++ r, '$-i) (l', §0^(m+1) ++ r', goto n X Y).
Proof using NP_spec.
pose dummy := ([§0], [§0], 0, +|, +|).
rewrite /maybe_increase_no_grow_time.
have [? | /in_iPI [j [n Hjn]]]: length P <= i \/ i < length P by lia.
{
exists dummy.
apply: terminal_maybe_reachable.
by apply: large_increase_terminal.
}
move: l => [|a l].
{
exists dummy.
by apply: terminal_maybe_reachable => ? /increase_no_step_shape.
}
case: a.
{
exists dummy.
by apply: terminal_maybe_reachable => ? /increase_no_step_shape.
}
have [[m' ->]|] := list_symbol_shape l.
{
exists dummy.
apply: (maybe_first_step (increase_no_spec (i, (j, n))) (§0^m') (§0^m ++ r)); [ by lia | by auto with M | by rewrite ?app_norm | ].
rewrite ?app_norm.
apply: maybe_goto_1_futile.
by lia.
}
move=> [m' [+ ->]] => {}l.
have [e He] := maybe_bounded_yes_grow ([§1] ++ l) (§0^(m'+1) ++ r) m.
exists e.
move: e He => [[[[l' r'] n'] X'] Y'] He.
apply: (maybe_first_step (increase_no_spec (i, (j, n))) (§0^m' ++ [§1] ++ l) (§0^m ++ r)); [by lia | by auto with M | by rewrite ?app_norm | ].
rewrite ?app_norm.
apply: (maybe_first_goto_1 1); first by lia.
move: He.
apply: maybe_reachable_mon'; first by lia.
rewrite ?app_norm.
do 5 f_equal.
Admitted.

Lemma maybe_index_yes_grow l r m i: exists '(l', r', n, X, Y), maybe_reachable maybe_index_yes_grow_time (l, §0^m ++ r, '#+i) (l', §0^(m+1) ++ r', goto n X Y).
Proof using NP_spec.
rewrite /maybe_index_yes_grow_time.
pose dummy := ([§0], [§0], 0, +|, +|).
have [[n ->] | ] := list_symbol_shape r.
{
exists dummy.
apply: (maybe_reachable_mon' (n := maybe_index_yes_futile_time)); [ by lia | by rewrite ?app_norm; reflexivity | by apply: maybe_index_yes_futile].
}
move=> [m' [+ ->]] => {}r.
have [Hi | /in_iPI [j [n Hijn]]]: length P <= i \/ i < length P by lia.
{
exists dummy.
apply: terminal_maybe_reachable.
by apply: large_index_terminal.
}
rewrite ?app_norm.
suff: exists '(l', r', n, X, Y), maybe_reachable maybe_index_yes_grow_time (l, §0^(m+m') ++ [§1] ++ r, '#+i) (l', §0^((m+m')+1) ++ r', goto n X Y).
{
move=> [[[[[l' r'] n'] X'] Y'] H].
exists (l', §0^m' ++ r', n', X', Y').
move: H.
apply: maybe_reachable_mon'; first by (rewrite /maybe_index_yes_grow_time; lia).
rewrite ?app_norm.
do 5 f_equal.
by lia.
}
move: (m + m') => {}m {m'}.
rewrite /maybe_index_yes_grow_time.
move: m => [|m].
{
move: l => [|a l].
{
exists dummy.
apply: (maybe_first_step (index_yes_spec_1 (i, (j, n))) [] r); [by lia | by auto with M | done |].
by apply: terminal_maybe_reachable => ? /index_try_step_shape [? ?].
}
case: a.
{
have [/in_iPI [j'] [n'] Hjj'n' | Hj] : j < length P \/ length P <= j by lia.
{
exists (([§1] ++ r), l, n', (#+j), (#-j)).
apply: (maybe_first_step (index_yes_spec_1 (i, (j, n))) ([§0] ++ l) r); [by lia | by auto with M | done |].
by apply: (maybe_first_step (index_try_spec (j, (j', n'))) r l); [by lia | by auto with M | done | by apply: maybe_reachable_refl'].
}
exists dummy.
apply: (maybe_first_step (index_yes_spec_1 (i, (j, n))) ([§0] ++ l) r); [by lia | by auto with M | done |].
apply: terminal_maybe_reachable.
by apply: large_index_terminal.
}
exists dummy.
apply: (maybe_first_step (index_yes_spec_1 (i, (j, n))) ([§1] ++ l) r); [by lia | by auto with M | done |].
apply: terminal_maybe_reachable.
by move=> ? /index_try_step_shape [? ?].
}
have [[k ->] |] := list_symbol_shape l.
{
exists dummy.
have [? | ?]: S m < n + 1 \/ n + 1 <= S m by lia.
{
apply: terminal_maybe_reachable=> ? /(index_yes_step_shape Hijn) [|/zero_prefix_lt]; [ done | by lia].
}
apply: (maybe_first_step (index_yes_spec_n1 (i, (j, n))) (§0^k) (§0^(m-n) ++ [§1] ++ r)); [by lia | by auto with M | by rewrite ?app_norm; do 4 f_equal; lia | ].
rewrite ?app_norm.
apply: maybe_goto_1_futile.
by lia.
}
move=> [k1] [l' ->].
have [|]:= list_symbol_shape l'.
{
move=> [k2 ->].
pose k := (S m) / (1+n).
have [? | ?] : k <= k2 \/ k2 < k by lia.
{
have [/in_iPI [j'] [n'] Hjj'n' | Hj]: j < length P \/ length P <= j by lia.
{
have := maybe_increase_next [] r i j n (S m) k2 k1 Hijn ltac:(lia).
move Hm': (k1 + S m + S m / (1 + n) + S m mod (1 + n)) => m'.
move: (k2 - S m / (1 + n)) => m'' H.
have ? := @div_mod_pos n m.
exists (([§1] ++ r), (§0^(m' - (S m + 1)) ++ [§1] ++ §0^m''), n', (#+j), (#-j)).
move: H.
apply: (maybe_reachable_trans' 1); [by lia | by rewrite ?app_norm |].
apply: (maybe_first_step (index_try_spec (j, (j', n'))) r (§0^(m'-1) ++ [§1] ++ §0^m'')); [by lia | by auto with M | by rewrite ?app_norm; do 4 f_equal; lia |].
apply: maybe_reachable_refl'.
rewrite ?app_norm.
do 4 f_equal.
by lia.
}
exists dummy.
have := maybe_increase_next [] r i j n (S m) k2 k1 Hijn ltac:(lia).
apply: (maybe_reachable_trans' 0); [by lia | by rewrite ?app_norm |].
apply: terminal_maybe_reachable.
by apply: large_index_terminal.
}
exists dummy.
have := maybe_increase_stop r i j n (S m) k2 k1 ([§0], §0^(S m + 1) ++ [§0], goto 0 +| +|) Hijn ltac:(lia).
by apply: maybe_reachable_mon'; first by lia.
}
move=> [k2] [{}l' ->].
pose k := (S m) / (1+n).
have [? | ?]: k <= k2 \/ k2 < k by lia.
{
have [/in_iPI [j'] [n'] Hjj'n' | Hj] : j < length P \/ length P <= j by lia.
{
have := maybe_increase_next ([§1] ++ l') r i j n (S m) k2 k1 Hijn ltac:(lia).
move Hm': (k1 + S m + S m / (1 + n) + S m mod (1 + n)) => m'.
move: (k2 - S m / (1 + n)) => m'' H.
have ? := @div_mod_pos n m.
exists (([§1] ++ r), (§0^(m' - (S m + 1)) ++ [§1] ++ §0^m'' ++ [§1] ++ l'), n', (#+j), (#-j)).
move: H.
apply: (maybe_reachable_trans' 1); [by lia | by rewrite ?app_norm |].
apply: (maybe_first_step (index_try_spec (j, (j', n'))) r (§0^(m'-1) ++ [§1] ++ §0^m'' ++ [§1] ++ l')); [by lia | by auto with M | by rewrite ?app_norm; do 4 f_equal; lia |].
apply: maybe_reachable_refl'.
rewrite ?app_norm.
do 4 f_equal.
by lia.
}
exists dummy.
have := maybe_increase_next ([§1] ++ l') r i j n (S m) k2 k1 Hijn ltac:(lia).
apply: (maybe_reachable_trans' 0); [by lia | by rewrite ?app_norm |].
apply: terminal_maybe_reachable.
by apply: large_index_terminal.
}
have [[[[[l'' r''] n''] X''] Y''] Hz] := maybe_bounded_yes_grow ([§1] ++ r) ([§1] ++ l') (S m + k1 + k2 + 1).
exists (l'', (§0^(k1 + k2 + 1) ++ r''), n'', X'', Y'').
have := maybe_increase_fail l' r i j n (S m) k2 k1 Hijn ltac:(lia).
apply: (maybe_reachable_trans' 1); [by lia | done |].
move: Hz.
apply: maybe_reachable_mon'; first by lia.
rewrite ?app_norm.
do 5 f_equal.
Admitted.

Lemma maybe_index_try_grow l r m i : exists '(l', r', n, X, Y), maybe_reachable maybe_index_try_grow_time (l, §0^m ++ r, '#?i) (l', §0^(m+1) ++ r', goto n X Y).
Proof using NP_spec.
rewrite /maybe_index_try_grow_time.
pose dummy := ([§0], [§0], 0, +|, +|).
have [[n ->]|] := list_symbol_shape r.
{
exists dummy.
apply: (maybe_reachable_mon' (n := maybe_index_try_futile_time)); [by lia | by rewrite ?app_norm; reflexivity | by apply: maybe_index_try_futile].
}
move=> [n [+ ->]] => {}r.
move Hk: (length P - i) => k.
suff: exists '(l', r', n', X', Y'), maybe_reachable (maybe_index_try_futile_time + k * maybe_index_try_step_time + maybe_index_yes_grow_time + maybe_goto_1_time + 1) (l, §0^(m+n) ++ [§1] ++ r, '#? i) (l', §0^((m+n)+1) ++ r', goto n' X' Y').
{
move=> [[[[[l' r'] n'] X'] Y'] H].
exists (l', §0^n ++ r', n', X', Y').
move: H.
apply: maybe_reachable_mon'; first by (rewrite /maybe_index_try_grow_time; lia).
rewrite ?app_norm.
do 5 f_equal.
by lia.
}
move: (m + n) l => {}m {n} [|a l].
{
exists dummy.
by apply: terminal_maybe_reachable => ? /index_try_step_shape [? ?].
}
case: a.
{
exists dummy.
by apply: terminal_maybe_reachable => ? /index_try_step_shape [? ?].
}
move: r m => r [|m].
{
exists dummy.
by apply: terminal_maybe_reachable => ? /index_try_step_shape [? ?].
}
elim: k i r Hk.
{
move=> *.
exists dummy.
apply: terminal_maybe_reachable.
apply: large_index_terminal.
by lia.
}
move=> k IH i r Hk /=.
have /in_iPI [j [n Hijn]] : i < length P by lia.
pose x := {| CM.state := i; CM.value := S m |}.
move Hi'm': (CM.step P x) => [i' m'].
have := CM_facts.step_progress P x.
move /(_ ltac:(rewrite /x /=; lia) ltac:(rewrite /x /=; lia)).
case.
{
rewrite Hi'm'.
move=> [? ?].
subst i' m'.
have [e He] := IH (1+i) r ltac:(lia).
exists e.
move: e He => [[[[? ?] ?] ?] ?] He.
have := maybe_index_try_step l r x.
rewrite /x Hi'm' /= ?nat_norm ?app_norm.
by apply: (maybe_reachable_trans' (maybe_index_try_futile_time + k * maybe_index_try_step_time + maybe_index_yes_grow_time + maybe_goto_1_time + 1)); first by lia.
}
move=> Hx.
have [[j' n'] [/nth_error_Some_In_iP HxIp /= Hmn']] := CM_facts.inc_value_mod Hx.
have [e He] := maybe_index_yes_grow ([§1] ++ r) ([§1] ++ l) (S m) i.
exists e.
move: e He => [[[[? ?] ?] ?] ?] He.
apply: (maybe_first_step (index_try_spec (i, (j, n))) l (§0^m ++ [§1] ++ r)); [ by nia | by auto with M | by rewrite ?app_norm | ].
rewrite ?app_norm.
apply: (maybe_first_goto_1 maybe_index_yes_grow_time); first by nia.
subst x.
have [_ ->]:= in_iP_unique (n := n) (n' := n') ltac:(eassumption) ltac:(eassumption).
rewrite Hmn'.
move: He.
Admitted.

Lemma maybe_increase_try_grow l r m i : exists '(l', r', n, X, Y), maybe_reachable 1 (l, §0^m ++ r, '$?i) (l', §0^(m+1) ++ r', goto n X Y).
Proof.
pose dummy := ([§0], [§0], 0, +|, +|).
have [? | /in_iPI [j] [n] ?]: length P <= i \/ i < length P by lia.
{
exists dummy.
apply: terminal_maybe_reachable.
by apply: large_increase_terminal.
}
move: l => [|a [|b l]].
-
exists dummy.
by apply: terminal_maybe_reachable => ? /increase_try_step_shape [|].
-
exists dummy.
by apply: terminal_maybe_reachable => ? /increase_try_step_shape [|].
-
case: a.
{
exists dummy.
by apply: terminal_maybe_reachable => ? /increase_try_step_shape [|].
}
case: b.
*
exists (([§1] ++ l), r, 0, ($+i), ($+i)).
apply: (maybe_first_step (increase_try_spec_0 (i, (j, n))) l (§0^m ++ r)); [by lia | by auto with M | done |].
rewrite ?app_norm.
apply: maybe_reachable_refl'.
do 4 f_equal.
by lia.
*
exists (([§1] ++ l), r, 0, ($-i), ($-i)).
apply: (maybe_first_step (increase_try_spec_1 (i, (j, n))) l (§0^m ++ r)); [by lia | by auto with M | done |].
rewrite ?app_norm.
apply: maybe_reachable_refl'.
do 4 f_equal.
Admitted.

Lemma maybe_increase_yes_grow l r m i : exists '(l', r', n, X, Y), maybe_reachable maybe_increase_yes_grow_time (l, §0^m ++ r, '$+i) (l', §0^(m+1) ++ r', goto n X Y).
Proof using NP_spec.
pose dummy := ([§0], [§0], 0, +|, +|).
rewrite /maybe_increase_yes_grow_time.
have [? | /in_iPI [j [n Hijn]]]: length P <= i \/ i < length P by lia.
{
exists dummy.
apply: terminal_maybe_reachable.
by apply: large_increase_terminal.
}
move: l => [|a l].
{
exists dummy.
by apply: terminal_maybe_reachable => ? /increase_yes_step_shape.
}
case: a.
{
exists dummy.
by apply: terminal_maybe_reachable => ? /increase_yes_step_shape.
}
have [|]:= list_symbol_shape l.
{
move=> [m' ->].
exists dummy.
apply: (maybe_first_step (increase_yes_spec (i, (j, n))) (§0^m') (§0^m ++ r)); [ by lia | by auto with M | by rewrite ?app_norm | ].
apply: (maybe_reachable_mon' (n := maybe_index_yes_futile_time)); [by lia | by rewrite ?app_norm; reflexivity | by apply: maybe_index_yes_futile].
}
move=> [m' [+ ->]] => {}l.
have [-> |] : m' = 0 \/ (0 < m' /\ m' < n+1) \/ n+1 <= m' by lia.
{
have [e He] := maybe_index_try_grow ([§1] ++ l) (§0^1 ++ r) m j.
exists e.
move: e He => [[[[l' r'] n'] X'] Y'] He.
apply: (maybe_first_step (increase_yes_spec (i, (j, n))) ([§1] ++ l) (§0^m ++ r)); [by lia | by auto with M | by rewrite ?app_norm | ].
apply: (maybe_first_step (index_yes_spec_1 (i, (j, n))) (§0^(1 + m) ++ r) l); [by lia | by auto with M | by rewrite ?app_norm | ].
move: He.
apply: maybe_reachable_mon'; first by lia.
rewrite ?app_norm.
do 5 f_equal.
by lia.
}
case=> Hm'.
{
exists dummy.
apply: (maybe_first_step (increase_yes_spec (i, (j, n))) (§0^m' ++ [§1] ++ l) (§0^m ++ r)); [ by lia | by auto with M | by rewrite ?app_norm |].
apply: terminal_maybe_reachable.
rewrite ?app_norm.
have ->: m' = 1+(m'-1) by lia.
move=> ? /(index_yes_step_shape Hijn) [| /zero_prefix_lt]; by [| lia].
}
exists (([§1] ++ §0^(m' - (n + 1)) ++ [§1] ++ l), (§0^n ++ r), 0, $?i, $?i).
apply: (maybe_first_step (increase_yes_spec (i, (j, n))) (§0^m' ++ [§1] ++ l) (§0^m ++ r)); [ by lia | by auto with M | by rewrite ?app_norm |].
apply: (maybe_first_step (index_yes_spec_n1 (i, (j, n))) (§0^(1+m) ++ r) (§0^(m'-(n+1)) ++ [§1] ++ l)); [ by lia | by auto with M | by rewrite ?app_norm; do 4 f_equal; lia |].
apply: maybe_reachable_refl'.
rewrite ?app_norm.
do 4 f_equal.
Admitted.

Lemma maybe_index_no_grow l r m i : exists '(l', r', n, X, Y), maybe_reachable maybe_index_no_grow_time (l, §0^m ++ r, '#-i) (l', §0^(m+1) ++ r', goto n X Y).
Proof using NP_spec.
pose dummy := ([§0], [§0], 0, +|, +|).
rewrite /maybe_index_no_grow_time.
have [? | /in_iPI [j [n Hjn]]] : length P <= i \/ i < length P by lia.
{
exists dummy.
apply: terminal_maybe_reachable.
by apply: large_index_terminal.
}
case: (list_symbol_shape r).
{
move=> [m' ->].
exists dummy.
rewrite ?app_norm.
case: (m + m').
{
by apply: terminal_maybe_reachable => ? /index_no_step_shape.
}
move=> {}m'.
apply: (maybe_first_step (index_no_spec (i, (j, n))) l (§0^m')); [by lia | by auto with M | by rewrite ?app_norm |].
rewrite ?app_norm.
apply: maybe_goto_1_futile.
by lia.
}
move=> [m' [+ ->]] => {}r.
rewrite ?app_norm.
move Hm'': (m + m') => m''.
move: m'' Hm'' => [|m''] Hm''.
{
exists dummy.
by apply: terminal_maybe_reachable => ? /index_no_step_shape.
}
have [e He] := maybe_index_try_grow ([§1] ++ r) (§0^m' ++ l) m (1+i).
exists e.
move: e He => [[[[l' r'] n'] X'] Y'] He.
apply: (maybe_first_step (index_no_spec (i, (j, n))) l (§0^m'' ++ [§1] ++ r)); [by lia | by auto with M | by rewrite ?app_norm | ].
rewrite ?app_norm.
apply: (maybe_first_goto_1 maybe_index_try_grow_time); first by lia.
move: He.
Admitted.

Lemma maybe_bounded_try_grow l r m : exists '(l', r', n, X, Y), maybe_reachable maybe_bounded_try_grow_time (l, §0^m ++ r, '?|) (l', §0^(m+1) ++ r', goto n X Y).
Proof using NP_spec.
rewrite /maybe_bounded_try_grow_time.
move: m => [|m]; first last.
{
exists ([], [], 0, +|, +|).
by apply: terminal_maybe_reachable => ? /bound_try_step_shape [? ?].
}
have [e He] := maybe_bounded_yes_grow r l 0.
exists e.
move: e He => [[[[l' r'] n] X] Y] He.
have := maybe_bounded_try r l.
Admitted.

Lemma maybe_basic_state_grow l r m X : exists '(l', r', n', X', Y'), maybe_reachable maybe_basic_state_grow_time (l, §0^m ++ r, basic_state X) (l', §0^(m+1) ++ r', goto n' X' Y').
Proof using NP_spec.
rewrite /maybe_basic_state_grow_time.
case: X.
-
case.
+
have [e He] := maybe_bounded_yes_grow l r m.
exists e.
move: e He => [[[[l' r'] n'] X'] Y'].
by apply: maybe_reachable_mon'; [ lia | ].
+
have [e He] := maybe_bounded_try_grow l r m.
exists e.
move: e He => [[[[l' r'] n'] X'] Y'].
by apply: maybe_reachable_mon'; [ lia | ].
-
case=> i.
+
have [e He] := maybe_index_try_grow l r m i.
exists e.
move: e He => [[[[l' r'] n'] X'] Y'].
by apply: maybe_reachable_mon'; [ lia | ].
+
have [e He] := maybe_index_yes_grow l r m i.
exists e.
move: e He => [[[[l' r'] n'] X'] Y'].
by apply: maybe_reachable_mon'; [ lia | ].
+
have [e He] := maybe_index_no_grow l r m i.
exists e.
move: e He => [[[[l' r'] n'] X'] Y'].
by apply: maybe_reachable_mon'; [ lia | ].
-
case=> i.
+
have [e He] := maybe_increase_try_grow l r m i.
exists e.
move: e He => [[[[l' r'] n'] X'] Y'].
by apply: maybe_reachable_mon'; [ lia | ].
+
have [e He] := maybe_increase_yes_grow l r m i.
exists e.
move: e He => [[[[l' r'] n'] X'] Y'].
by apply: maybe_reachable_mon'; [ lia | ].
+
have [e He] := maybe_increase_no_grow l r m i.
exists e.
move: e He => [[[[l' r'] n'] X'] Y'].
Admitted.

Lemma maybe_first_goto_1 T l r T' n X Y c Z : T + maybe_goto_1_time <= T' -> maybe_reachable T ([§1] ++ r, §0^c ++ l, basic_state (if c mod (n+1) is 0 then X else Y)) Z -> maybe_reachable T' (l, §0^c ++ [§1] ++ r, goto n X Y) Z.
Proof using NP_spec.
move=> ? ?.
have := maybe_goto_1 l r n X Y c.
by (apply: (maybe_reachable_trans' T); first by lia).
