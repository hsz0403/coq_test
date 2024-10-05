From Undecidability.Shared.Libs.PSL Require Import Base.
Require Import Coq.Vectors.Fin.
Ltac destruct_fin i := lazymatch type of i with | Fin.t (S ?n) => let i' := fresh i in pose proof fin_destruct_S i as [ (i'&->) | -> ]; [ destruct_fin i' | idtac] | Fin.t O => pose proof fin_destruct_O i as [] | Fin.t (_ + _) => let i' := fresh i in pose proof fin_destruct_add i as [ (i'&->) | (i'&->)];destruct_fin i' | Fin.t _ => idtac end.
Goal True.
Proof.
assert (i : Fin.t 4) by repeat constructor.
enough (i = i) by tauto.
destruct_fin i.
all: reflexivity.

Lemma Fin_L_fillive (n m : nat) (i1 i2 : Fin.t n) : Fin.L m i1 = Fin.L m i2 -> i1 = i2.
Proof.
induction n as [ | n' IH].
-
destruct_fin i1.
-
destruct_fin i1; destruct_fin i2; cbn in *; auto; try congruence.
intros H%Fin.FS_inj.
now apply IH in H as ->.
