Require Import InfSeqExt.infseq.
Section sec_exteq.
Variable T: Type.
CoInductive exteq : infseq T -> infseq T -> Prop := exteq_intro : forall x s1 s2, exteq s1 s2 -> exteq (Cons x s1) (Cons x s2).
End sec_exteq.
Arguments exteq [T] _ _.
Arguments exteq_inversion [T x1 s1 x2 s2] _.
Arguments exteq_refl [T] _.
Arguments exteq_sym [T] _ _ _.
Arguments exteq_trans [T] _ _ _ _ _.
Section sec_exteq_congruence.
Variable T: Type.
Definition extensional (P: infseq T -> Prop) := forall s1 s2, exteq s1 s2 -> P s1 -> P s2.
End sec_exteq_congruence.
Arguments extensional [T] _.
Arguments extensional_True_tl [T] _ _ _ _.
Arguments extensional_False_tl [T] _ _ _ _.
Arguments extensional_and_tl [T P Q] _ _ _ _ _ _.
Arguments extensional_or_tl [T P Q] _ _ _ _ _ _.
Arguments extensional_impl_tl [T P Q] _ _ _ _ _ _ _.
Arguments extensional_not_tl [T P] _ _ _ _ _ _.
Arguments extensional_now [T P] _ _ _ _.
Arguments extensional_next [T P] _ _ _ _ _.
Arguments extensional_consecutive [T P] _ _ _ _.
Arguments extensional_always [T P] _ _ _ _ _.
Arguments extensional_weak_until [T P Q] _ _ _ _ _ _.
Arguments extensional_until [T P Q] _ _ _ _ _ _.
Arguments extensional_release [T P Q] _ _ _ _ _ _.
Arguments extensional_eventually [T P] _ _ _ _ _.
Arguments extensional_inf_often [T P] _ _ _ _ _.
Arguments extensional_continuously [T P] _ _ _ _ _.

Lemma exteq_trans : forall s1 s2 s3, exteq s1 s2 -> exteq s2 s3 -> exteq s1 s3.
Proof using.
cofix cf.
intros (x1, s1) (x2, s2) (x3, s3) e12 e23.
case (exteq_inversion _ _ _ _ e12); clear e12; intros e12 ex12.
case (exteq_inversion _ _ _ _ e23); clear e23; intros e23 ex23.
rewrite e12; rewrite e23.
constructor.
apply cf with s2; assumption.
