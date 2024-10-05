Require Import List.
Import ListNotations.
Require Import Undecidability.PCP.PCP.
Require Import Undecidability.Synthetic.Definitions.
Require Import ssreflect ssrbool ssrfun.
Set Default Goal Selector "!".
Definition bin (x: list nat) : list bool := flat_map (fun (a : nat) => true :: (repeat false a) ++ [true]) x.
Definition bin_map A := map (fun '(x, y) => (bin x, bin y)) A.

Lemma eq_binP {x y} : x = y <-> (bin x) = (bin y).
Proof.
elim: x y; first by case.
move=> a x IH [|b y /=]; first done.
constructor; first by move=> [<- <-].
case.
elim: a b.
{
case; last done.
by move=> [/IH ->].
}
move=> a IH2 [|b /=]; first done.
by move=> [/IH2 [<- <-]].
