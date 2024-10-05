From Undecidability.Shared.Libs.PSL Require Import Base.
Require Import Coq.Vectors.Fin.
Ltac destruct_fin i := lazymatch type of i with | Fin.t (S ?n) => let i' := fresh i in pose proof fin_destruct_S i as [ (i'&->) | -> ]; [ destruct_fin i' | idtac] | Fin.t O => pose proof fin_destruct_O i as [] | Fin.t (_ + _) => let i' := fresh i in pose proof fin_destruct_add i as [ (i'&->) | (i'&->)];destruct_fin i' | Fin.t _ => idtac end.
Goal True.
Proof.
assert (i : Fin.t 4) by repeat constructor.
enough (i = i) by tauto.
destruct_fin i.
all: reflexivity.

Lemma fin_destruct_add : forall (n m : nat) (i : Fin.t (n+m)), {i' : Fin.t n | i = Fin.L _ i'} + {i' : Fin.t m | i = Fin.R _ i'}.
Proof.
induction n;cbn.
right.
now eauto.
intros ? i.
destruct (fin_destruct_S i) as [[i' ->]| ->].
-
destruct (IHn _ i') as [ [? ->] | [? ->]].
--
left.
now eexists (Fin.FS _).
--
right.
eauto.
-
left.
now exists Fin.F1.
