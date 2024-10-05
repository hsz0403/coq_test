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

Lemma transport {p: list constraint} : SSemiU p -> RU2SemiU (σ false p, σ true p, τ p).
Proof.
move=> [φ'] [ψ0'] [ψ1'] /Forall_forall Hp.
exists (φ φ'), (ψ φ' ψ0'), (ψ φ' ψ1').
suff: forall i, substitute (ψ φ' (if i then ψ1' else ψ0')) (substitute (φ φ') (σ i p)) = substitute (φ φ') (τ p) by (move=> H; rewrite (H false) (H true)).
move=> i.
elim: p Hp.
-
by move: i => [|] _ /=; rewrite /φ ?enumP /= /ψ ?enumP /=.
-
move=> [[a x] [y b]] p IH /=.
rewrite Forall_norm /=.
move => [+ /IH <-].
move Hφ'y: (φ' y) => φ'y.
case: φ'y Hφ'y; first done.
move=> s t Hφ'y Hst {IH}.
Admitted.

Lemma reflection {p: list constraint} : RU2SemiU (σ false p, σ true p, τ p) -> SSemiU p.
Proof.
move=> [φ] [ψ0] [ψ1] [Hψ0 Hψ1].
exists (fun x => φ (to_nat (x, 0))), ψ0, ψ1.
rewrite -Forall_forall.
elim: p Hψ0 Hψ1; first done.
move=> [[a x] [y b]] p IH /= [Hψ0 ?] [Hψ1 ?].
rewrite Forall_norm /=.
constructor; [| by apply: IH].
Admitted.

Theorem reduction : SSemiU ⪯ RU2SemiU.
Proof.
exists (fun p => (Argument.σ false p, Argument.σ true p, Argument.τ p)).
intro p.
constructor.
-
exact Argument.transport.
-
Admitted.

Lemma substitute_ψP {φ' ψ': valuation} {t: term} : substitute (ψ φ' ψ') (substitute embed_var t) = substitute embed_var (substitute ψ' t).
Proof.
elim: t => [x | *] /=; [by rewrite /ψ ?enumP | by f_equal].
