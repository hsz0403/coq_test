Set Implicit Arguments.
Require Import FinFun.
From Undecidability.HOU Require Import std.decidable.
Inductive diag: nat -> nat -> Type := | diagB: diag 0 0 | diagC: forall m, diag 0 m -> diag (S m) 0 | diagS: forall n m, diag (S n) m -> diag n (S m).
Fixpoint diagStepR m n (d: diag m n) : diag m (S n) := match d with | diagB => diagS (diagC diagB) | diagC H => diagS (diagC (diagStepR H)) | diagS H => diagS (diagStepR H) end.
Fixpoint diagStepL m n (d: diag m n) : diag (S m) n := match d with | diagB => diagC diagB | diagC H => diagC (diagS (diagStepL H)) | diagS H => diagS (diagStepL H) end.
Fixpoint diagZero (a: nat) : diag 0 a := match a with | 0 => diagB | S a => diagStepR (diagZero a) end.
Fixpoint diagId m n: diag m n := match m with | O => diagZero n | S m => diagStepL (diagId m n) end.
Definition I__P (p: nat * nat) := let (m, n) := p in diag_rect (fun _ _ _ => nat) 0 (fun _ _ => S) (fun _ _ _ => S) (diagId m n): nat.
Fixpoint R__P (n: nat) : nat * nat := match n with | 0 => (0,0) | S n => match R__P n with | (0, b) => (S b, 0) | (S a, b) => (a, S b) end end.
Require Import Arith Lia Nat Arith.Div2.
Definition I__S (s: nat + nat) := match s with | inl n => double n | inr n => S (double n) end.
Definition R__S (n: nat) := if even n then inl (div2 n) else inr (div2 n).
Arguments I__P p : simpl never.
Arguments R__P n : simpl never.
Arguments I__S s : simpl never.
Arguments R__S n : simpl never.

Lemma injective_I__S : Injective I__S.
Proof.
intros s s' H % (f_equal R__S).
now rewrite !R__S_I__S in H.
