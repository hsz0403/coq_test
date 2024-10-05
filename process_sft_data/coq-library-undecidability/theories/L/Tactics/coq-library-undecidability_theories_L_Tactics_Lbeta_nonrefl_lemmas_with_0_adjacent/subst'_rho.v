From Undecidability.L Require Import ComputableTactics Lproc mixedTactics Tactics.Computable ComputableTime Lrewrite.
Import L_Notations.
Local Fixpoint subst' (s : term) (k : nat) (u : term) {struct s} : term := match s with | # n => if Init.Nat.eqb n k then u else # n | app s0 t => (subst' s0 k u) (subst' t k u) | (lam s0) => (lam (subst' s0 (S k) u)) end.
Ltac redStep':= match goal with |- _ == _ => apply star_equiv;redStep' | |- app (lam ?s) ?t >* _ => apply lStep;[now Lproc|reflexivity] | |- app ?s ?t >* _ => progress (etransitivity;[apply star_step_app_proper;redStep'|]);[reflexivity] | |- _ => reflexivity end.
Ltac redStep2 := etransitivity;[redStep'|].
Ltac Lbeta_old := cbn [subst' Init.Nat.eqb].
Local Ltac closedRewrite2 := rewrite ?subst'_int; match goal with | [ |- context[subst' ?s _ _] ] => let cl := fresh "cl" in assert (cl:closed s) by Lproc; let cl' := fresh "cl'" in assert (cl':= subst'_cls cl); rewrite ?cl';clear cl;clear cl' end.
Ltac closedRewrite3' := match goal with | |- app _ _ = _ => try etransitivity;[progress (apply app_eq_proper;closedRewrite3';reflexivity)|] | |- lam _ = _ => apply lam_app_proper;closedRewrite3' | |- rho _ = _ => eapply f_equal;Lbeta_old;closedRewrite3' | |- subst' (subst' _ _ _) _ _ = _ => etransitivity;[apply subst'_eq_proper;closedRewrite3'|closedRewrite3'] | |- subst' (subst' _ _ _) _ _ = _ => etransitivity;[apply subst'_eq_proper;closedRewrite3'|closedRewrite3'] | |- subst' (ext _) _ _ = _ => apply subst'_int | |- subst' (rho _) _ _ = _ => rewrite subst'_rho;f_equal;closedRewrite3' | |- subst' _ _ _ = _ => apply subst'_cls;now Lproc | |- _ => reflexivity end.
Ltac closedRewrite3 := etransitivity;[cbn;(eapply clR||eapply clR');closedRewrite3';reflexivity|].
Ltac Lred' := (progress redStep2); Lbeta_old.
Tactic Notation "redStep" := Lred';closedRewrite3.
Ltac redSteps := progress (reflexivity || ((repeat Lred');closedRewrite3)).
Ltac LsimplRed := repeat ( redSteps ; try Lrewrite).

Lemma subst'_rho s x u : subst' (rho s) x u = rho (subst' s (S x) u).
Proof.
reflexivity.
