From Undecidability.L.Functions Require Export Eval.
From Undecidability.L.Tactics Require Import Lbeta_nonrefl.
Section hoas.
Import HOAS_Notations.
Definition Por :term := Eval simpl in [L_HOAS λ s t , (λ n0, !!(ext doesHaltIn) s n0 ) (!!mu (λ n ,!!(ext orb) (!!(ext doesHaltIn) s n) (!!(ext doesHaltIn) t n)))] .
End hoas.
Hint Resolve Por_proc : LProc.
Import L_Notations.

Lemma Por_proc : proc Por.
Proof.
unfold Por; Lproc.
