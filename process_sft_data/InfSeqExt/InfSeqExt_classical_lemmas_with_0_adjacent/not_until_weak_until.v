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

Lemma not_until_weak_until : forall (J P : infseq T -> Prop) (s : infseq T), ~ until J P s -> weak_until (J /\_ ~_ P) (~_ J /\_ ~_ P) s.
Proof using.
intros J P.
cofix c.
intros s.
case (classic (P s)).
-
intros Ps un.
contradict un.
apply U0.
assumption.
-
intros Ps.
case (classic (J s)); destruct s as [x s].
*
intros Js un.
apply W_tl.
+
unfold and_tl, not_tl.
split; trivial.
+
simpl.
apply c.
intros unn.
contradict un.
apply U_next; trivial.
*
intros Js un.
apply W0.
split; trivial.
