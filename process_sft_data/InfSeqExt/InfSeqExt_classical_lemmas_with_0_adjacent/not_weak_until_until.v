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

Lemma not_weak_until_until : forall (J P : infseq T -> Prop) (s : infseq T), ~ weak_until J P s -> until (J /\_ ~_ P) (~_ J /\_ ~_ P) s.
Proof using.
intros J P s wun.
case (classic (until (J /\_ ~_ P) (~_ J /\_ ~_ P) s)); trivial.
intros un.
contradict wun.
revert s un.
cofix c.
intros s.
case (classic (P s)).
-
intros Ps un.
apply W0.
assumption.
-
intros Ps.
case (classic (J s)); destruct s as [x s].
*
intros Js un.
apply W_tl; trivial.
simpl.
apply c.
intros unn.
contradict un.
apply U_next; trivial.
split; trivial.
*
intros Js un.
contradict un.
apply U0.
split; trivial.
