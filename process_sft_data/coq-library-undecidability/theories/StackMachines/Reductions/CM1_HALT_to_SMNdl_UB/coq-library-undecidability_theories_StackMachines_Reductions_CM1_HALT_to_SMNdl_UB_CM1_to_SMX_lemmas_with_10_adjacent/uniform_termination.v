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

Lemma maybe_goto_1_grow l r m n X Y : exists '(l', r', n', X', Y'), maybe_reachable maybe_goto_1_grow_time (l, §0^m ++ r, goto n X Y) (l', §0^(m+1) ++ r', goto n' X' Y').
Proof using NP_spec.
rewrite /maybe_goto_1_grow_time.
case: (list_symbol_shape r).
{
move=> [m' ->].
exists ([], [], 0, +|, +|).
rewrite /maybe_basic_state_grow_time ?app_norm.
apply: maybe_goto_1_futile.
by lia.
}
move=> [m' [+ ->]] => {}r.
rewrite ?app_norm.
move Hk: ((m + m') mod (n + 1)) => k.
move: k Hk => [|k] Hk.
{
have [e He] := maybe_basic_state_grow ([§1] ++ r) (§0^m' ++ l) m X.
exists e.
move: e He => [[[[l' r'] n'] X'] Y'] He.
apply: (maybe_first_goto_1 maybe_basic_state_grow_time); first by lia.
rewrite Hk.
move: He.
apply: maybe_reachable_mon'; [by lia | by rewrite ?app_norm].
}
have [e He] := maybe_basic_state_grow ([§1] ++ r) (§0^m' ++ l) m Y.
exists e.
move: e He => [[[[l' r'] n'] X'] Y'] He.
apply: (maybe_first_goto_1 maybe_basic_state_grow_time); first by lia.
rewrite Hk.
move: He.
Admitted.

Lemma maybe_goto_1_grow_iter l r m n X Y : exists '(l', r', n', X', Y'), maybe_reachable (m*maybe_goto_1_grow_time) (l, r, goto n X Y) (l', §0^m ++ r', goto n' X' Y').
Proof using NP_spec.
elim: m l r n X Y.
{
move=> l r n X Y.
exists (l, r, n, X, Y).
by apply: maybe_reachable_refl'.
}
move=> m + l r n X Y.
move /(_ l r n X Y) => [[[[[l' r'] n'] X'] Y'] He'].
have [e He] := maybe_goto_1_grow l' r' m n' X' Y'.
exists e.
move: e He => [[[[l'' r''] n''] X''] Y''] He.
move: He'.
Admitted.

Lemma reachable_configurations {T x z} : reachable_n T x z -> terminal M z -> exists L, (forall y, SM.reachable M x y -> In y L) /\ length L <= S T.
Proof.
elim: T x z.
{
move=> x z.
move HT: (0) => T Hxz.
case: Hxz HT; last done.
move=> ? {}x <- Hx.
exists [x].
constructor; last by (move=> /=; lia).
move=> y /clos_rt_rt1n_iff Hxy.
case: Hxy Hx; first by (move=> *; left).
by move=> > + ? Hx => /Hx.
}
move=> T IH x z.
move HT': (S T) => T' Hxz.
case: Hxz HT'.
{
move=> ? {}x <- Hx.
exists [x].
constructor; last by (move=> /=; lia).
move=> y /clos_rt_rt1n_iff Hxy.
case: Hxy Hx; first by (move=> *; left).
by move=> > + ? Hx => /Hx.
}
move=> {}T' {}x y {}z Hxy Hyz ?.
have ?: T = T' by lia.
subst T'.
move /(IH y _ Hyz) => [L [H1L H2L]].
exists (x :: L).
constructor; first last.
{
rewrite /length -/(length _).
by lia.
}
move=> y'.
move HT': (1 + T) => T' /clos_rt_rt1n_iff Hxy'.
case: Hxy' HT' Hxy; first by (move=> *; left).
move=> {}y' z' Hxy' Hy'z' ? Hxy.
right.
apply: H1L.
have -> : y = y' by apply: deterministic_M; eassumption.
Admitted.

Theorem terminating_P_to_bounded_M : SM.bounded M (1+uniform_termination_time).
Proof using NP_spec.
rewrite /SM.bounded.
move=> x.
have [z [Hz]]:= uniform_termination x.
Admitted.

Theorem uniform_termination x: exists z, reachable_n uniform_termination_time x z /\ terminal M z.
Proof using NP_spec.
apply: universal_maybe_reachable_terminal => z.
rewrite /uniform_termination_time.
move: x => [[l r] [X|n X Y]].
{
have [[[[[l' r'] n'] X'] Y']] := maybe_basic_state_grow l r 0 X.
apply: (maybe_reachable_trans' ((G + (CP + 1)) * maybe_goto_1_grow_time + (NP * step_time CP TP + 2))); [ by lia | done | ].
have [[[[[l'' r''] n''] X''] Y'']] := maybe_goto_1_grow_iter l' (§0^1 ++ r') (G + (CP + 1)) n' X' Y'.
apply: (maybe_reachable_trans' (NP * step_time CP TP + 2)); [ by lia | done | ].
apply: maybe_goto_1_far; by lia.
}
have [[[[[l'' r''] n''] X''] Y'']] := maybe_goto_1_grow_iter l r (G + (CP + 1)) n X Y.
apply: (maybe_reachable_trans' (NP * step_time CP TP + 2)); [ by lia | done | ].
apply: maybe_goto_1_far; by lia.
