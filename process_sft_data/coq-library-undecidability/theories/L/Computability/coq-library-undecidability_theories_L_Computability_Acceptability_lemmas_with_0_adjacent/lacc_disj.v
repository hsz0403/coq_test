From Undecidability.L Require Export LTerm Por Decidability Lbeta_nonrefl.
Import L_Notations.
Definition pi (s t:term) := converges (s (ext t)).
Definition lacc (P : term -> Prop) := exists u, proc u /\ forall t, P t <-> pi u t.
Goal forall s1 s2 t, s1 == s2 -> (pi s1 t <-> pi s2 t).
Proof.
intros s1 s2 t H; intuition; unfold pi; [now rewrite <- H | now rewrite H].
Definition acc_conj (p q : term) := lam ((lam (q #1)) (p #0) ).
Hint Unfold acc_conj : cbv.

Lemma lacc_disj M N : lacc M -> lacc N -> lacc (disj M N).
Proof.
intros [u [[lam_u cls_u] Hu]] [v [[lam_v cls_v] Hv]].
unfold lacc, disj.
exists (lam (Por ((ext app) (enc u) ((ext (term_enc) #0))) (((ext app) (enc v) ((ext (term_enc)) #0))))).
split.
Lproc.
intros t.
rewrite Hu, Hv; unfold pi.
evar (t':term).
assert (R':(lam( (Por ((ext app) (ext u) ((ext (term_enc)) 0))) ((ext app) (ext v) ((ext (term_enc)) 0))) (ext t)) >* t').
subst t'.
now Lsimpl.
rewrite R'.
subst t'.
split.
intros [A|B].
-
destruct (Por_correct_1a (v (enc t)) A) as [s [R ls]].
exists s.
split;try Lproc.
eassumption.
-
destruct (Por_correct_1b (u (enc t)) B) as [s [R ls]].
exists s.
split;try Lproc.
eassumption.
-
intros [s [H ls]].
edestruct Por_correct_2 as [].
{
exists s.
split;auto.
rewrite !ext_is_enc.
unfold Por.
rewrite <- R'.
Lsimpl.
eassumption.
}
apply Por_correct' in H0.
destruct x;auto.
