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

Lemma not_always_eventually_not : forall (P : infseq T -> Prop) (s : infseq T), ~ always P s -> eventually (~_ P) s.
Proof using.
intros P s alP.
case (classic ((eventually (~_ P)) s)); trivial.
intros evP.
apply not_eventually_not_always in evP.
contradict alP.
assumption.
