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

Lemma extensional_or_tl : forall (P Q: infseq T -> Prop), extensional P -> extensional Q -> extensional (P \/_ Q).
Proof using.
intros P Q eP eQ s1 s2 e.
destruct e; simpl.
unfold or_tl.
intuition.
-
left; apply eP with (Cons x s1); [constructor; assumption | assumption].
-
right; apply eQ with (Cons x s1); [constructor; assumption | assumption].
