Require Import InfSeqExt.infseq.
Require Import Classical.
Section sec_classical.
Variable T : Type.
End sec_classical.
Arguments weak_until_until_or_always [T J P s] _.
Arguments not_until_weak_until [T J P s] _.
Arguments not_weak_until_until [T J P s] _.
Arguments not_eventually_not_always [T P s] _.
Arguments not_always_eventually_not [T P s] _.
Arguments not_until_release [T J P s] _.
Arguments not_release_until [T J P s] _.
Arguments not_inf_often_continuously_not [T P s] _.
Arguments not_continously_inf_often_not [T P s] _.
Arguments not_tl_and_tl_or_tl [T P Q s] _.

Lemma not_continously_inf_often_not : forall (P : infseq T -> Prop) (s : infseq T), ~ continuously P s -> inf_often (~_ P) s.
Proof using.
intros P.
cofix c.
intros [x s] cnyP.
apply Always.
-
unfold continuously in cnyP.
apply not_eventually_always_not in cnyP.
apply always_now in cnyP.
unfold not_tl in cnyP.
apply not_always_eventually_not in cnyP.
assumption.
-
apply c.
intros cnynP.
contradict cnyP.
apply E_next.
assumption.
