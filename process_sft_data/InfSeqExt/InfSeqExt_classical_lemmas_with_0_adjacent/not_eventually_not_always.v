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

Lemma not_eventually_not_always : forall (P : infseq T -> Prop) (s : infseq T), ~ eventually (~_ P) s -> always P s.
Proof using.
intros P.
cofix c.
intro s.
destruct s as [e s].
intros evnP.
apply Always.
-
case (classic (P (Cons e s))); trivial.
intros orP.
apply (E0 _ (~_ P)) in orP.
contradict evnP.
assumption.
-
apply c.
simpl.
intros evP.
contradict evnP.
apply E_next.
assumption.
