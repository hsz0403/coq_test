From Undecidability.L.Functions Require Export Eval.
From Undecidability.L.Tactics Require Import Lbeta_nonrefl.
Section hoas.
Import HOAS_Notations.
Definition Por :term := Eval simpl in [L_HOAS λ s t , (λ n0, !!(ext doesHaltIn) s n0 ) (!!mu (λ n ,!!(ext orb) (!!(ext doesHaltIn) s n) (!!(ext doesHaltIn) t n)))] .
End hoas.
Hint Resolve Por_proc : LProc.
Import L_Notations.

Lemma Por_correct_1b (s t:term) : converges t -> converges (Por (ext s) (ext t)).
Proof.
intros H.
apply eval_converges in H as [t' H].
apply eval_seval in H as [n H].
apply seval_eva in H.
edestruct mu_complete with (n:=n) (P:=lam ( (ext orb) ((ext doesHaltIn) (ext s) 0) ((ext doesHaltIn) (ext t) 0))) as [v R].
-
Lproc.
-
eexists;now Lsimpl.
-
Lsimpl.
edestruct (doesHaltIn t n) eqn:eq;unfold doesHaltIn in eq;rewrite H in eq.
2:congruence.
edestruct doesHaltIn;reflexivity.
-
eapply Seval.eval_converges.
unfold Por.
Lsimpl_old.
rewrite R.
Lsimpl.
Lreflexivity.
