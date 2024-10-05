Require Import List Lia.
Import ListNotations.
Require Import Undecidability.StackMachines.Util.Nat_facts.
Require Import ssreflect ssrbool ssrfun.
Set Default Goal Selector "!".

Lemma nth_error_seq {m l n: nat} : n < l -> nth_error (seq m l) n = Some (m+n).
Proof.
elim: n m l.
-
move=> m [|l]; first by lia.
move=> /= _.
congr Some.
by lia.
-
move=> n IH m [|l /= ?]; first by lia.
rewrite /nth_error -/(nth_error _ _) IH; [|congr Some]; by lia.
