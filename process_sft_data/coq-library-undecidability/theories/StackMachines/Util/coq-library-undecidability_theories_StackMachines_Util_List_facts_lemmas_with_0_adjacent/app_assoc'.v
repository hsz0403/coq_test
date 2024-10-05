Require Import List Lia.
Import ListNotations.
Require Import Undecidability.StackMachines.Util.Nat_facts.
Require Import ssreflect ssrbool ssrfun.
Set Default Goal Selector "!".

Lemma app_assoc' {X: Type} {xs ys zs: list X} : (xs ++ ys) ++ zs = xs ++ ys ++ zs.
Proof.
by rewrite app_assoc.
