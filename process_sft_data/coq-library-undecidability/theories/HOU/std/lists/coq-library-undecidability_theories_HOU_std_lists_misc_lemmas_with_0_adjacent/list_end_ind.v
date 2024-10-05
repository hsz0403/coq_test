Set Implicit Arguments.
Require Import List Lia.
Import ListNotations.

Lemma list_end_ind: forall (A : Type) (P : list A -> Prop), P [] -> (forall (a : A) (l : list A), P l -> P (l ++ [a])) -> forall l : list A, P l.
Proof.
intros A P H IH l.
specialize (rev_list_ind P H) as Ind.
rewrite <-rev_involutive.
eapply Ind.
intros; cbn; now apply IH.
