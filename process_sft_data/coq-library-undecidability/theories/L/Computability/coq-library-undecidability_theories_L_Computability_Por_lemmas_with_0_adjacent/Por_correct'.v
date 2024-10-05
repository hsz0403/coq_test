From Undecidability.L.Functions Require Export Eval.
From Undecidability.L.Tactics Require Import Lbeta_nonrefl.
Section hoas.
Import HOAS_Notations.
Definition Por :term := Eval simpl in [L_HOAS λ s t , (λ n0, !!(ext doesHaltIn) s n0 ) (!!mu (λ n ,!!(ext orb) (!!(ext doesHaltIn) s n) (!!(ext doesHaltIn) t n)))] .
End hoas.
Hint Resolve Por_proc : LProc.
Import L_Notations.

Lemma Por_correct' (s t:term) (b:bool) : Por (ext s) (ext t) == ext b -> if b then converges s else converges t.
Proof.
intros H.
unfold Por in H.
LsimplHypo.
evar (s':term).
assert (C:converges s').
eexists.
split.
exact H.
Lproc.
subst s'.
apply app_converges in C as [_ [v [C lv]]].
assert (C':= C).
apply mu_sound in C'; try Lproc.
-
destruct C' as [n [eq [R C']]].
subst v.
rewrite C in H.
LsimplHypo.
Lrewrite in R.
Lrewrite in H.
apply enc_extinj in H.
rewrite H in R.
destruct b.
+
unfold doesHaltIn in H.
destruct (eva n s) eqn: eq.
apply eva_seval in eq.
apply seval_eval in eq.
eauto.
congruence.
+
simpl in R.
apply enc_extinj in R.
unfold doesHaltIn in R.
destruct (eva n t) eqn: eq.
apply eva_seval in eq.
apply seval_eval in eq.
eauto.
congruence.
-
intros.
eexists.
now Lsimpl.
