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

Theorem fmap_bound n P : (forall x, x < n -> ex (P x)) -> exists m, forall x, x < n -> exists y, y < m /\ P x y.
Proof with try lia.
revert P; induction n as [ | n IHn ]; intros P HP.
+
exists 0; intros...
+
destruct (HP 0) as (m0 & H0)...
destruct (IHn (fun n => P (S n))) as (m1 & Hm1).
-
intros; apply HP...
-
exists (1+m0+m1); intros [ | x ] Hx.
*
exists m0; split; auto...
*
destruct (Hm1 x) as (y & H1 & H2)...
exists y; split; auto...
