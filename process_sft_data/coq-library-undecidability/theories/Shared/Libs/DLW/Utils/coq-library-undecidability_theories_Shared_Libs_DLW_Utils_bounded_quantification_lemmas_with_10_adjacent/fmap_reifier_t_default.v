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
Admitted.

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
Admitted.

Theorem fmap_reifier_default X n (P : nat -> X -> Prop) : inhabited X -> (forall x, x < n -> ex (P x)) -> exists f, forall x, x < n -> P x (f x).
Proof with try lia.
intros [ u ].
revert P; induction n as [ | n IHn ]; intros P HP.
+
exists (fun _ => u); intros...
+
destruct (IHn (fun i => P (S i))) as (f & Hf).
{
intros; apply HP...
}
destruct (HP 0) as (x & Hx)...
exists (fun i => match i with 0 => x | S i => f i end).
Admitted.

Theorem fmap_reifer_bound n P : (forall x, x < n -> ex (P x)) -> exists m f, forall x, x < n -> f x < m /\ P x (f x).
Proof.
intros H.
apply fmap_bound in H.
destruct H as (m & Hm); exists m.
Admitted.

Theorem fmmap_bound p n (P : nat -> (nat -> nat) -> Prop) : (forall x f g, equal_upto p f g -> P x f -> P x g) -> (forall x, x < n -> exists f, P x f) -> exists m, forall x, x < n -> exists f, (forall i, i < p -> f i < m) /\ P x f.
Proof.
revert P.
induction p as [ | p IHp ]; intros P HP H.
+
exists 1; intros x Hx.
destruct (H _ Hx) as (f & Hf).
exists (fun _ => 0); split; auto.
apply (HP x f); auto.
intros ? ?; lia.
+
set (Q x y := exists f, P x (fun i => match i with 0 => y | S i => f i end)).
destruct (@fmap_bound n Q) as (m1 & Hm1).
{
intros x Hx.
destruct (H _ Hx) as (f & Hf).
exists (f 0); red.
exists (fun i => f (S i)).
revert Hf; apply HP.
intros [ | i ]; auto.
}
set (R x f := exists y, y < m1 /\ P x (fun i => match i with 0 => y | S i => f i end)).
destruct (IHp R) as (m2 & Hm2).
{
intros x f g Hfg (y & H1 & H2); exists y; split; auto.
revert H2; apply HP; intros [ | ]; auto; intros; apply Hfg; lia.
}
{
intros x Hx.
destruct (Hm1 _ Hx) as (y & H1 & f & H2).
exists f, y; split; auto.
}
exists (m1+m2).
intros x Hx.
destruct (Hm2 _ Hx) as (f & H1 & y & H2 & H3).
eexists; split; [ | exact H3 ].
intros [ | j ] Hj; try lia.
Admitted.

Theorem fmmap_reifer_bound p n (P : nat -> (nat -> nat) -> Prop) : (forall x f g, equal_upto p f g -> P x f -> P x g) -> (forall x, x < n -> exists f, P x f) -> exists m f, forall x, x < n -> (forall j, j < p -> f x j < m) /\ P x (f x).
Proof.
intros H1 H2.
apply fmmap_bound with (1 := H1) in H2.
destruct H2 as (m & Hm).
apply fmap_reifier_default in Hm; auto.
Admitted.

Definition fmap_reifier_t_default X (Q : nat -> X -> Prop) k (x : X) : (forall i, i < k -> sig (Q i)) -> { f : nat -> X | forall i, i < k -> Q i (f i) }.
Proof.
intros H.
apply fmap_reifier_t in H.
destruct H as (f & Hf).
exists (fun i => match le_lt_dec k i with | left _ => x | right Hi => f i Hi end).
intros i Hi.
destruct (le_lt_dec k i) as [ H1 | ]; auto.
exfalso; revert Hi H1; apply lt_not_le.
