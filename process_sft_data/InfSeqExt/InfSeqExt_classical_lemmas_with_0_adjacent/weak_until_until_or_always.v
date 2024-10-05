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

Lemma weak_until_until_or_always : forall (J P : infseq T -> Prop) (s : infseq T), weak_until J P s -> until J P s \/ always J s.
Proof using.
intros J P s.
case (classic (eventually P s)).
-
intros evP wu.
left.
induction evP.
*
apply U0.
assumption.
*
apply weak_until_Cons in wu.
case wu.
+
intros PC.
apply U0.
assumption.
+
intros [Js wu'].
apply U_next; trivial.
apply IHevP.
assumption.
-
intros evP wu.
right.
apply not_eventually_always_not in evP.
apply weak_until_always_not_always in wu; trivial.
