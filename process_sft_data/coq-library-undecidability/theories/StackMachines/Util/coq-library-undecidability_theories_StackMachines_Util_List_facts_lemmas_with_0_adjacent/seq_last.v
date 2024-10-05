Require Import List Lia.
Import ListNotations.
Require Import Undecidability.StackMachines.Util.Nat_facts.
Require Import ssreflect ssrbool ssrfun.
Set Default Goal Selector "!".

Lemma seq_last {m n} : seq m (1+n) = seq m n ++ [m + n].
Proof.
have -> : 1+n = n+1 by lia.
by rewrite seq_app.
