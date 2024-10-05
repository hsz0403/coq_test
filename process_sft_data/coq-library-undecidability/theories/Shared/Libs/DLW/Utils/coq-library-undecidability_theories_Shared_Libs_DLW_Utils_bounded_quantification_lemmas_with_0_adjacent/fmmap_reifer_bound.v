Require Import Arith Lia.
Set Implicit Arguments.
Definition fmap_reifier_t X (Q : nat -> X -> Prop) k : (forall i, i < k -> sig (Q i)) -> { f : forall i, i < k -> X | forall i Hi, Q i (f i Hi) }.
Proof.
revert Q; induction k as [ | k IHk ]; intros Q HQ.
+
assert (f : forall i, i < 0 -> X) by (intros i Hi; exfalso; revert Hi; apply Nat.nlt_0_r).
exists f; intros i Hi; exfalso; revert Hi; apply Nat.nlt_0_r.
+
destruct (HQ 0) as (f0 & H0).
*
apply Nat.lt_0_succ.
*
destruct (IHk (fun i => Q (S i))) as (f & Hf).
-
intros; apply HQ, lt_n_S; trivial.
-
set (f' := fun i => match i return i < S k -> X with | 0 => fun _ => f0 | S j => fun Hj => f j (lt_S_n _ _ Hj) end).
exists f'; intros [ | i ] Hi; simpl; trivial.
Defined.
Definition fmap_reifier_t_default X (Q : nat -> X -> Prop) k (x : X) : (forall i, i < k -> sig (Q i)) -> { f : nat -> X | forall i, i < k -> Q i (f i) }.
Proof.
intros H.
apply fmap_reifier_t in H.
destruct H as (f & Hf).
exists (fun i => match le_lt_dec k i with | left _ => x | right Hi => f i Hi end).
intros i Hi.
destruct (le_lt_dec k i) as [ H1 | ]; auto.
exfalso; revert Hi H1; apply lt_not_le.
Defined.
Local Notation equal_upto := (fun m (f g : nat -> nat) => forall n, n < m -> f n = g n).

Theorem fmmap_reifer_bound p n (P : nat -> (nat -> nat) -> Prop) : (forall x f g, equal_upto p f g -> P x f -> P x g) -> (forall x, x < n -> exists f, P x f) -> exists m f, forall x, x < n -> (forall j, j < p -> f x j < m) /\ P x (f x).
Proof.
intros H1 H2.
apply fmmap_bound with (1 := H1) in H2.
destruct H2 as (m & Hm).
apply fmap_reifier_default in Hm; auto.
destruct Hm as (f & Hf); exists m, f; auto.
