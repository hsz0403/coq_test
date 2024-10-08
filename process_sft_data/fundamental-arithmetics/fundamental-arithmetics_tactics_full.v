Require Import Bool.
Ltac and_elim := match goal with | [H:_ /\ _ |- _ ] => elim H;clear H;intro H;intro;and_elim | _ => idtac end.
Ltac andb_elim := match goal with | [H:andb _ _ = true |- _ ] => elim (andb_prop _ _ H);clear H;intro H;intro;and_elim | _ => idtac end.
Ltac ex_elim H x := elim H;clear H;intro x;intro H;and_elim.
Ltac or_elim H := (case H;clear H;intro H;[idtac | or_elim H]) || idtac.
Ltac clear_all := match goal with | [id:_ |- _] => clear id;clear_all | [ |- _] => idtac end.
Require Import Arith.
Require Import Omega.
Ltac try_absurd_arith := try (elim (lt_irrefl 0);omega).