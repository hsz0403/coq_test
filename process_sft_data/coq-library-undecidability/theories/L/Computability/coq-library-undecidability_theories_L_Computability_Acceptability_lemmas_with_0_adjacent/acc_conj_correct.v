From Undecidability.L Require Export LTerm Por Decidability Lbeta_nonrefl.
Import L_Notations.
Definition pi (s t:term) := converges (s (ext t)).
Definition lacc (P : term -> Prop) := exists u, proc u /\ forall t, P t <-> pi u t.
Goal forall s1 s2 t, s1 == s2 -> (pi s1 t <-> pi s2 t).
Proof.
intros s1 s2 t H; intuition; unfold pi; [now rewrite <- H | now rewrite H].
Definition acc_conj (p q : term) := lam ((lam (q #1)) (p #0) ).
Hint Unfold acc_conj : cbv.

Lemma acc_conj_correct p q s : closed p -> closed q -> (pi (acc_conj p q) s <-> pi p s /\ pi q s).
Proof.
intros cls_p cls_q.
split.
-
intros [x [Hx lx]].
assert (H : converges (lam( q (enc s)) (p (enc s)))).
{
exists x;split;auto.
symmetry.
symmetry in Hx.
unfold acc_conj in Hx.
rewrite Hx.
redStep.
LsimplRed.
}
destruct (app_converges H) as [_ [y [Hy ly]]].
split.
+
eexists; split;eassumption.
+
exists x;split;auto.
rewrite <- Hx.
symmetry.
clear Hx.
unfold acc_conj.
LsimplRed.
rewrite Hy.
LsimplRed.
-
intros [[x [Hx ?]] [y [Hy ?]]].
exists y.
split.
unfold acc_conj.
LsimplRed.
rewrite Hx.
LsimplRed.
tauto.
Lproc.
