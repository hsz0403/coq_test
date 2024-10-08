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

Lemma subst'_eq s k u: subst s k u = subst' s k u.
Proof.
Admitted.

Lemma lStep s t u: lambda t -> (subst' s 0 t) >* u -> (lam s) t >* u.
Proof.
intros.
rewrite <- H0.
apply step_star_subrelation.
rewrite <- subst'_eq.
Admitted.

Lemma subst'_cls s : closed s -> forall x t, subst' s x t = s.
Proof.
intros.
rewrite <- subst'_eq.
Admitted.

Lemma app_eq_proper (s s' t t' :term) : s = s' -> t = t' -> s t = s' t'.
Proof.
Admitted.

Lemma lam_app_proper (s s' :term) : s = s' -> lam s = lam s'.
Proof.
Admitted.

Lemma subst'_eq_proper (s s':term) x t : s = s' -> subst' s x t = subst' s' x t.
Proof.
Admitted.

Lemma clR s s' t : s' = s -> s >* t -> s' >* t.
Proof.
Admitted.

Lemma clR' s s' t : s' = s -> s == t -> s' == t.
Proof.
Admitted.

Lemma subst'_rho s x u : subst' (rho s) x u = rho (subst' s (S x) u).
Proof.
Admitted.

Lemma subst'_int (X:Set) (ty : TT X) (f:X) (H : computable f) : forall x t, subst' (ext f) x t = (ext f).
Proof.
intros.
apply subst'_cls.
Lproc.
