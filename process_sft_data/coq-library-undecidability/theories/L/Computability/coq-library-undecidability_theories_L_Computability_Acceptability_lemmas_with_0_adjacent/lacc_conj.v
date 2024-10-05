From Undecidability.L Require Export LTerm Por Decidability Lbeta_nonrefl.
Import L_Notations.
Definition pi (s t:term) := converges (s (ext t)).
Definition lacc (P : term -> Prop) := exists u, proc u /\ forall t, P t <-> pi u t.
Goal forall s1 s2 t, s1 == s2 -> (pi s1 t <-> pi s2 t).
Proof.
intros s1 s2 t H; intuition; unfold pi; [now rewrite <- H | now rewrite H].
Definition acc_conj (p q : term) := lam ((lam (q #1)) (p #0) ).
Hint Unfold acc_conj : cbv.

Lemma lacc_conj P Q : lacc P -> lacc Q -> lacc (conj P Q).
Proof.
intros [u1 [[? ?] Hu1]] [u2 [[? ?] Hu2]].
exists (acc_conj u1 u2).
split.
unfold acc_conj.
Lproc.
intros; rewrite acc_conj_correct; firstorder.
