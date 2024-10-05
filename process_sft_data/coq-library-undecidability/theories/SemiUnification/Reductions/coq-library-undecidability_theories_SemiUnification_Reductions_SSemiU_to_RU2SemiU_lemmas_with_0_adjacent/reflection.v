Require Import List.
Require Import Undecidability.SemiUnification.SemiU.
From Undecidability.SemiUnification.Util Require Import Facts Enumerable.
Require Import ssreflect ssrfun ssrbool.
Set Default Proof Using "Type".
Set Default Goal Selector "!".
Module Argument.
Definition embed_var (x: nat) := atom (to_nat (x, 0)).
Definition ρ (i a b: bool) (x y: nat) := match i, a, b with | false, true, _ => atom (to_nat (y, 1)) | true, false, _ => atom (to_nat (y, 1)) | _, _, false => arr (embed_var x) (atom (to_nat (y, 2))) | _, _, true => arr (atom (to_nat (y, 3))) (embed_var x) end.
Definition σ (i: bool) (p: list constraint) : term := fold_right (fun '((a, x), (y, b)) s => arr (ρ i a b x y) s) (atom (to_nat (0, 4))) p.
Definition τ (p: list constraint) : term := fold_right (fun '((a, x), (y, b)) t => arr (embed_var y) t) (atom (to_nat (0, 4))) p.
Definition src (t: term) := if t is arr s t then s else atom 0.
Definition tgt (t: term) := if t is arr s t then t else atom 0.
Definition φ (φ' : valuation) : valuation := fun x => match of_nat x with | (x, 0) => substitute embed_var (φ' x) | _ => atom x end.
Definition ψ (φ' ψ' : valuation) : valuation := fun x => match of_nat x with | (x, 0) => substitute embed_var (ψ' x) | (x, 1) => substitute embed_var (φ' x) | (x, 2) => substitute embed_var (tgt (φ' x)) | (x, 3) => substitute embed_var (src (φ' x)) | _ => atom x end.
End Argument.
Require Import Undecidability.Synthetic.Definitions.

Lemma reflection {p: list constraint} : RU2SemiU (σ false p, σ true p, τ p) -> SSemiU p.
Proof.
move=> [φ] [ψ0] [ψ1] [Hψ0 Hψ1].
exists (fun x => φ (to_nat (x, 0))), ψ0, ψ1.
rewrite -Forall_forall.
elim: p Hψ0 Hψ1; first done.
move=> [[a x] [y b]] p IH /= [Hψ0 ?] [Hψ1 ?].
rewrite Forall_norm /=.
constructor; [| by apply: IH].
by move: a Hψ0 Hψ1 => [_ <-| <- _]; move: b => [|].
