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

Lemma not_inf_often_continuously_not : forall (P : infseq T -> Prop) (s : infseq T), ~ inf_often P s -> continuously (~_ P) s.
Proof using.
intros P s ioP.
apply not_always_eventually_not in ioP.
induction ioP.
-
apply not_eventually_always_not in H.
apply E0.
assumption.
-
apply E_next.
assumption.
