Require Import List Lia.
Import ListNotations.
Require Import Undecidability.CounterMachines.CM2.
Require Import Undecidability.CounterMachines.Util.Nat_facts.
Require Import ssreflect.
Set Default Goal Selector "!".

Lemma values_ub cm c n : value1 (Nat.iter n (CM2.step cm) c) + value2 (Nat.iter n (CM2.step cm) c) <= n + value1 c + value2 c.
Proof.
move Hk : (n + value1 c + value2 c) => k.
have : n + value1 c + value2 c <= k by lia.
elim: n k c {Hk}; first done.
move=> n IH k [p a b].
rewrite -/(1 + n) iter_plus /=.
case: (nth_error cm p).
-
move=> [] [] => [||?|?]; move: a b => [|?] [|?] /= ?; apply: IH => /=; by lia.
-
move=> ?.
apply: IH => /=.
by lia.
