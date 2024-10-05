From Undecidability.L.Functions Require Export Eval.
From Undecidability.L.Tactics Require Import Lbeta_nonrefl.
Section hoas.
Import HOAS_Notations.
Definition Por :term := Eval simpl in [L_HOAS λ s t , (λ n0, !!(ext doesHaltIn) s n0 ) (!!mu (λ n ,!!(ext orb) (!!(ext doesHaltIn) s n) (!!(ext doesHaltIn) t n)))] .
End hoas.
Hint Resolve Por_proc : LProc.
Import L_Notations.

Lemma Por_correct_1 s t : converges s \/ converges t -> converges (Por (ext s) (ext t)).
Proof.
intros [convs | convt]; eauto using Por_correct_1a, Por_correct_1b.
