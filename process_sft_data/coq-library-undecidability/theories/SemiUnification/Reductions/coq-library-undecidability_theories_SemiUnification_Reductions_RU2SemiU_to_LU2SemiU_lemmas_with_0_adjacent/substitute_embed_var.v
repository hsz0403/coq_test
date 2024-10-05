Require Import List.
Require Import Undecidability.SemiUnification.SemiU.
From Undecidability.SemiUnification.Util Require Import Facts Enumerable.
Require Import ssreflect ssrfun ssrbool.
Set Default Proof Using "Type".
Set Default Goal Selector "!".
Module Argument.
Definition embed_var (x: nat) := atom (to_nat (x, 0)).
Definition z (b: bool) := atom (to_nat (0, if b then 2 else 1)).
Section RU2SemiU_LU2SemiU.
Variables s0 s1 t: term.
Definition s' := substitute embed_var (arr s0 s1).
Definition t0' := arr (substitute embed_var t) (z false).
Definition t1' := arr (z true) (substitute embed_var t).
Section Transport.
Variables φ ψ0 ψ1 : valuation.
Variable Hψ0 : substitute ψ0 (substitute φ s0) = substitute φ t.
Variable Hψ1 : substitute ψ1 (substitute φ s1) = substitute φ t.
Definition φ' : valuation := fun x => match of_nat x with | (x, 0) => substitute embed_var (φ x) | (0, 1) => substitute embed_var (substitute ψ0 (substitute φ s1)) | (0, 2) => substitute embed_var (substitute ψ1 (substitute φ s0)) | _ => atom x end.
Definition ψ0' : valuation := fun x => match of_nat x with | (x, 0) => substitute embed_var (ψ0 x) | _ => atom x end.
Definition ψ1' : valuation := fun x => match of_nat x with | (x, 0) => substitute embed_var (ψ1 x) | _ => atom x end.
End Transport.
Section Reflection.
Variables φ' ψ0' ψ1' : valuation.
Variable Hψ0' : substitute ψ0' (substitute φ' s') = substitute φ' t0'.
Variable Hψ1' : substitute ψ1' (substitute φ' s') = substitute φ' t1'.
End Reflection.
End RU2SemiU_LU2SemiU.
End Argument.
Require Import Undecidability.Synthetic.Definitions.

Lemma substitute_embed_var {ξ r} : substitute (fun x => ξ (to_nat (x, 0))) r = substitute ξ (substitute embed_var r).
Proof.
elim: r; [done | by move=> /=; congruence].
