From Undecidability.L.Functions Require Export Eval.
From Undecidability.L.Tactics Require Import Lbeta_nonrefl.
Section hoas.
Import HOAS_Notations.
Definition Por :term := Eval simpl in [L_HOAS λ s t , (λ n0, !!(ext doesHaltIn) s n0 ) (!!mu (λ n ,!!(ext orb) (!!(ext doesHaltIn) s n) (!!(ext doesHaltIn) t n)))] .
End hoas.
Hint Resolve Por_proc : LProc.
Import L_Notations.

Lemma Por_correct_2 (s t:term) : converges (Por (ext s) (ext t)) -> exists (b:bool), Por (ext s) (ext t) == ext b.
Proof.
intros [v [R lv]].
unfold Por in R.
LsimplHypo.
evar (s':term).
assert (C:converges s').
eexists.
split.
exact R.
Lproc.
subst s'.
apply app_converges in C as [_ [v' [C lv']]].
assert (C':=C).
apply mu_sound in C as [n [eq [R' H]]];try Lproc.
-
exists (doesHaltIn s n).
subst.
unfold Por.
Lsimpl_old.
rewrite C'.
now Lsimpl.
-
eexists.
now Lsimpl.
