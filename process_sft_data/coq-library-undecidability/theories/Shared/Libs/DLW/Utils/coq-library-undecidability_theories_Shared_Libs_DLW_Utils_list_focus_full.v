Require Import List.
Require Import Permutation.
From Undecidability.Shared.Libs.DLW.Utils Require Import focus utils_tac.
Ltac focus_g x ll := let rr := focus_lst x ll in replace ll with rr; [ idtac | solve_list_eq ].
Ltac focus_g_2 x ll := let rr := focus_lst_2 x ll in replace ll with rr; [ idtac | solve_list_eq ].
Ltac focus_g_3 x ll := let rr := focus_lst_3 x ll in replace ll with rr; [ idtac | solve_list_eq ].
Ltac focus_h H x ll := let rr := focus_lst x ll in replace ll with rr in H; [ idtac | solve_list_eq ].
Ltac focus_h_2 H x ll := let rr := focus_lst_2 x ll in replace ll with rr in H; [ idtac | solve_list_eq ].
Ltac focus_h_3 H x ll := let rr := focus_lst_3 x ll in replace ll with rr in H; [ idtac | solve_list_eq ].
Ltac focus_goal x ll := match type of x with | list _ => focus_g x ll | _ => focus_g (x::nil) ll end.
Ltac focus_goal_2 x ll := match type of x with | list _ => focus_g_2 x ll | _ => focus_g_2 (x::nil) ll end.
Ltac focus_goal_3 x ll := match type of x with | list _ => focus_g_3 x ll | _ => focus_g_3 (x::nil) ll end.
Ltac focus_hyp H x ll := match type of x with | list _ => focus_h H x ll | _ => focus_h H (x::nil) ll end.
Ltac focus_hyp_2 H x ll := match type of x with | list _ => focus_h_2 H x ll | _ => focus_h_2 H (x::nil) ll end.
Ltac focus_hyp_3 H x ll := match type of x with | list _ => focus_h_3 H x ll | _ => focus_h_3 H (x::nil) ll end.
Ltac chg_goal x := match goal with | |- context[?hh] => match type of hh with list _ => focus_goal x hh end end.
Ltac chg_goal_2 x := match goal with | |- context[?hh] => match type of hh with list _ => focus_goal_2 x hh end end.
Ltac chg_goal_3 x := match goal with | |- context[?hh] => match type of hh with list _ => focus_goal_3 x hh end end.
Ltac chg_hyp H x := let gg := fresh in match goal with |- ?G => set (gg := G) end; generalize H; match goal with | |- context[?hh] => intros _; match type of hh with | list _ => focus_hyp H x hh end end; unfold gg; clear gg.
Ltac chg_hyp_2 H x := let gg := fresh in match goal with |- ?G => set (gg := G) end; generalize H; match goal with | |- context[?hh] => intros _; match type of hh with | list _ => focus_hyp_2 H x hh end end; unfold gg; clear gg.
Ltac chg_hyp_3 H x := let gg := fresh in match goal with |- ?G => set (gg := G) end; generalize H; match goal with | |- context[?hh] => intros _; match type of hh with | list _ => focus_hyp_3 H x hh end end; unfold gg; clear gg.
Tactic Notation "focus" constr(X) := chg_goal X.
Tactic Notation "focus" constr(X) "in" hyp(H) := chg_hyp H X.
Tactic Notation "focus" constr(X) "at" "2" := chg_goal_2 X.
Tactic Notation "focus" constr(X) "in" hyp(H) "at" "2" := chg_hyp_2 H X.
Tactic Notation "focus" constr(X) "at" "3" := chg_goal_3 X.
Tactic Notation "focus" constr(X) "in" hyp(H) "at" "3" := chg_hyp_3 H X.