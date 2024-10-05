From Undecidability.Shared.Libs.PSL Require Import Base.
Require Import Coq.Vectors.Fin.
Ltac destruct_fin i := lazymatch type of i with | Fin.t (S ?n) => let i' := fresh i in pose proof fin_destruct_S i as [ (i'&->) | -> ]; [ destruct_fin i' | idtac] | Fin.t O => pose proof fin_destruct_O i as [] | Fin.t (_ + _) => let i' := fresh i in pose proof fin_destruct_add i as [ (i'&->) | (i'&->)];destruct_fin i' | Fin.t _ => idtac end.
Goal True.
Proof.
assert (i : Fin.t 4) by repeat constructor.
enough (i = i) by tauto.
destruct_fin i.
all: reflexivity.

Lemma fin_destruct_S (n : nat) (i : Fin.t (S n)) : { i' | i = Fin.FS i' } + { i = Fin.F1 }.
Proof.
Admitted.

Lemma fin_destruct_O (i : Fin.t 0) : Empty_set.
Proof.
Admitted.

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
Admitted.

Goal True.
Proof.
assert (i : Fin.t 4) by repeat constructor.
enough (i = i) by tauto.
destruct_fin i.
Admitted.

Lemma Fin_L_fillive (n m : nat) (i1 i2 : Fin.t n) : Fin.L m i1 = Fin.L m i2 -> i1 = i2.
Proof.
induction n as [ | n' IH].
-
destruct_fin i1.
-
destruct_fin i1; destruct_fin i2; cbn in *; auto; try congruence.
intros H%Fin.FS_inj.
Admitted.

Lemma Fin_eqb_R_R m n (i i' : Fin.t n): Fin.eqb (Fin.R m i) (Fin.R m i') = Fin.eqb i i'.
Proof.
induction m;cbn.
Admitted.

Lemma Fin_eqb_L_L m n (i i' : Fin.t n): Fin.eqb (Fin.L m i) (Fin.L m i') = Fin.eqb i i'.
Proof.
revert i i'.
induction n;intros i i'; destruct_fin i;destruct_fin i';cbn.
4:rewrite !Nat.eqb_refl.
Admitted.

Lemma Fin_eqb_R_L m n (i : Fin.t n) (i' : Fin.t m): Fin.eqb(Fin.R n i') (Fin.L m i) = false.
Proof.
revert m i i'.
induction n;intros m i i'; destruct_fin i;destruct_fin i';cbn.
Admitted.

Lemma Fin_eqb_L_R m n (i : Fin.t n) (i' : Fin.t m): Fin.eqb (Fin.L m i) (Fin.R n i') = false.
Proof.
revert m i i'.
induction n;intros m i i'; destruct_fin i;destruct_fin i';cbn.
Admitted.

Lemma Fin_R_fillive (n m : nat) (i1 i2 : Fin.t n) : Fin.R m i1 = Fin.R m i2 -> i1 = i2.
Proof.
induction m as [ | n' IH]; cbn.
-
auto.
-
intros H % Fin.FS_inj.
auto.
