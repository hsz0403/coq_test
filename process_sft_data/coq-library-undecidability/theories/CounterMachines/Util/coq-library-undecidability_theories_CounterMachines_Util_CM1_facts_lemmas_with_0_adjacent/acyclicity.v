Require Import List PeanoNat Lia.
Import ListNotations.
Require Import Undecidability.CounterMachines.CM1.
Require Import Undecidability.CounterMachines.Util.Nat_facts.
Require Import ssreflect ssrbool ssrfun.
Set Default Goal Selector "!".
Definition config_weight (M: Cm1) : Config -> nat := fun '{| state := p; value := v |} => p + length M * v.

Theorem acyclicity {M: Cm1} {n: nat} {x: Config} : not (halting M (Nat.iter n (step M) x)) -> NoDup (map (fun i => Nat.iter i (step M) x) (seq 0 (2+n))).
Proof.
elim: n.
{
move=> /= Hx.
apply: NoDup_cons; first by case.
by apply: NoDup_cons; [ case | apply: NoDup_nil ].
}
move=> n IH HSn.
have /IH : not (halting M (Nat.iter n (step M) x)).
{
move=> Hn.
apply: HSn.
move: Hn.
apply: halting_monotone.
by lia.
}
have ->: seq 0 (2 + S n) = seq 0 (2 + n) ++ [2 + n].
{
have ->: 2 + S n = (2 + n) + 1 by lia.
by rewrite [seq 0 (2 + n + 1)] seq_app.
}
rewrite map_app.
set f := (fun i : nat => Nat.iter i (step M) x).
have : Add (f (2+n)) (map f (seq 0 (2 + n)) ++ []) (map f (seq 0 (2 + n)) ++ map f [2 + n]) by apply: Add_app.
rewrite app_nil_r.
move /(@NoDup_Add Config) => H Hfn.
apply /H.
constructor; first done.
rewrite in_map_iff.
move=> [i].
rewrite in_seq /f.
move=> [+ ?].
have ->: 2 + n = i + (1 + (1+n - i)) by lia.
rewrite iter_plus.
set x' := Nat.iter i (step M) x.
move=> Hx'.
suff: config_weight M x' < config_weight M (Nat.iter (1 + (1+n - i)) (step M) x').
{
rewrite -Hx'.
by lia.
}
apply: config_weight_run_monotone.
subst x'.
rewrite -iter_plus.
by have ->: i + (1 + n - i) = S n by lia.
